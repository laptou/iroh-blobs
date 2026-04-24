//! WASM-only blob store backed by browser IndexedDB.
//!
//! Architecture: mirrors `mem.rs` (actor + `api::proto::Command` dispatch) but
//! persists chunk bodies in IDB instead of `SparseMemFile` vectors.  Only entry
//! metadata and tags are cached in-process; actual blob data stays in IDB and is
//! fetched per-request.
//!
//! Schema (DB name `iroh-blobs-wasm`, version 1):
//!   `entries`         – key hash_hex, value: JSON metadata
//!   `data_chunks`     – key "{hash_hex}|{idx:016x}", value: JS object {hash, data: Uint8Array}
//!   `outboard_chunks` – key "{hash_hex}|{node_idx:016x}", same value shape
//!   `tags`            – key hex(tag_bytes), value: JSON {hash, format}
//!
//! GC: uses `iroh_blobs::store::gc::gc_run_once`; no session cleanup on shutdown.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    future::Future,
    io,
    num::NonZeroU64,
    ops::Deref,
    rc::Rc,
};

use bao_tree::{
    blake3,
    io::{
        mixed::{traverse_ranges_validated, EncodedItem, ReadBytesAt},
        outboard::PreOrderMemOutboard,
        BaoContentItem, EncodeError, Leaf,
    },
    BaoTree, ChunkNum, ChunkRanges, TreeNode,
};
use bytes::Bytes;
use irpc::channel::mpsc;
use js_sys::Promise;
use n0_error::Result;
use n0_future::{
    task::{JoinError, JoinSet},
    time::SystemTime,
};
use range_collections::range_set::RangeSetRange;
use serde::{Deserialize, Serialize};
use tokio::sync::watch;
use tracing::{error, info, trace};
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use web_sys::{IdbDatabase, IdbKeyRange, IdbRequest, IdbTransactionMode};

use super::util::{BaoTreeSender, Tag};
use super::IROH_BLOCK_SIZE;
use crate::{
    api::{
        self,
        blobs::{AddProgressItem, Bitfield, BlobStatus, ExportProgressItem},
        proto::{
            BatchMsg, BatchResponse, BlobDeleteRequest, BlobStatusMsg, BlobStatusRequest, Command,
            CreateTagMsg, CreateTagRequest, CreateTempTagMsg, DeleteBlobsMsg, DeleteTagsMsg,
            DeleteTagsRequest, ExportBaoMsg, ExportBaoRequest, ExportRangesItem, ExportRangesMsg,
            ExportRangesRequest, ImportBaoMsg, ImportBaoRequest, ImportByteStreamMsg,
            ImportByteStreamUpdate, ImportBytesMsg, ImportBytesRequest, ListBlobsMsg, ListTagsMsg,
            ListTagsRequest, ObserveMsg, ObserveRequest, RenameTagMsg, RenameTagRequest, Scope,
            SetTagMsg, SetTagRequest, ShutdownMsg, SyncDbMsg, WaitIdleMsg,
        },
        tags::TagInfo,
        ApiClient,
    },
    protocol::ChunkRangesExt,
    util::temp_tag::{TagDrop, TempTagScope, TempTags},
    BlobFormat, Hash, HashAndFormat,
};

// ---------- constants ----------

const DB_NAME: &str = "iroh-blobs-wasm";
const DB_VERSION: u32 = 1;
const STORE_ENTRIES: &str = "entries";
const STORE_DATA_CHUNKS: &str = "data_chunks";
const STORE_OUTBOARD: &str = "outboard_chunks";
const STORE_TAGS: &str = "tags";

// ---------- IDB request → Future bridge ----------

/// Converts an `IdbRequest` into a JS `Promise` that resolves with the request result.
/// Closures are cloned inside the FnMut callback (never captured before the move).
fn await_request(req: IdbRequest) -> JsFuture {
    let p = Promise::new(&mut |resolve, reject| {
        // clone inside the FnMut body so we can move into FnOnce inner closures
        let req_ok = req.clone();
        let on_success = Closure::once(move |_: web_sys::Event| {
            let val = req_ok.result().unwrap_or(JsValue::UNDEFINED);
            resolve.call1(&JsValue::NULL, &val).ok();
        });
        req.set_onsuccess(Some(on_success.as_ref().unchecked_ref()));
        on_success.forget();

        let req_err = req.clone();
        let on_error = Closure::once(move |_: web_sys::Event| {
            let err = req_err
                .error()
                .ok()
                .flatten()
                .map(JsValue::from)
                .unwrap_or_else(|| JsValue::from_str("idb error"));
            reject.call1(&JsValue::NULL, &err).ok();
        });
        req.set_onerror(Some(on_error.as_ref().unchecked_ref()));
        on_error.forget();
    });
    JsFuture::from(p)
}

/// IDB open-request needs separate `onsuccess` / `onupgradeneeded`.
async fn open_db(db_name: &str, version: u32) -> io::Result<IdbDatabase> {
    let window = web_sys::window().ok_or_else(|| io::Error::other("no window"))?;
    let idb = window
        .indexed_db()
        .map_err(|_| io::Error::other("cannot access indexeddb"))?
        .ok_or_else(|| io::Error::other("indexeddb not available"))?;
    let open_req = idb
        .open_with_u32(db_name, version)
        .map_err(|_| io::Error::other("idb open failed"))?;

    // upgrade callback runs synchronously during `onupgradeneeded`
    let on_upgrade = Closure::<dyn FnMut(web_sys::IdbVersionChangeEvent)>::new(
        |event: web_sys::IdbVersionChangeEvent| {
            let target = event.target().unwrap();
            let req = target
                .dyn_into::<web_sys::IdbOpenDbRequest>()
                .unwrap();
            let db = req
                .result()
                .unwrap()
                .dyn_into::<IdbDatabase>()
                .unwrap();
            if let Err(e) = setup_schema(&db) {
                error!("idb schema setup failed: {e:?}");
            }
        },
    );
    open_req.set_onupgradeneeded(Some(on_upgrade.as_ref().unchecked_ref()));
    on_upgrade.forget();

    let result = await_request(open_req.into())
        .await
        .map_err(|e| io::Error::other(format!("idb open await: {e:?}")))?;
    result
        .dyn_into::<IdbDatabase>()
        .map_err(|_| io::Error::other("idb result is not a database"))
}

fn store_exists(names: &web_sys::DomStringList, name: &str) -> bool {
    for i in 0..names.length() {
        if names.item(i).as_deref() == Some(name) {
            return true;
        }
    }
    false
}

fn setup_schema(db: &IdbDatabase) -> io::Result<()> {
    let names = db.object_store_names();
    if !store_exists(&names, STORE_ENTRIES) {
        db.create_object_store(STORE_ENTRIES)
            .map_err(|_| io::Error::other("create entries store"))?;
    }
    if !store_exists(&names, STORE_DATA_CHUNKS) {
        db.create_object_store(STORE_DATA_CHUNKS)
            .map_err(|_| io::Error::other("create data_chunks store"))?;
    }
    if !store_exists(&names, STORE_OUTBOARD) {
        db.create_object_store(STORE_OUTBOARD)
            .map_err(|_| io::Error::other("create outboard_chunks store"))?;
    }
    if !store_exists(&names, STORE_TAGS) {
        db.create_object_store(STORE_TAGS)
            .map_err(|_| io::Error::other("create tags store"))?;
    }
    Ok(())
}

// ---------- serialised record types ----------

/// Metadata stored per-hash in the `entries` object store.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct EntryRecord {
    hash: String,
    complete: bool,
    /// validated / known total size
    size: u64,
    bitfield: Bitfield,
}

/// `{hash, format}` stored in the `tags` object store.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct TagRecord {
    hash: String,
    /// 0 = Raw, 1 = HashSeq
    format: u8,
}

fn hash_to_hex(h: &Hash) -> String {
    hex::encode(h.as_bytes())
}

fn hex_to_hash(s: &str) -> io::Result<Hash> {
    let mut bytes = [0u8; 32];
    hex::decode_to_slice(s, &mut bytes).map_err(io::Error::other)?;
    Ok(Hash::from(bytes))
}

fn tag_to_hex(t: &Tag) -> String {
    hex::encode(t.as_ref())
}

fn hex_to_tag(s: &str) -> io::Result<Tag> {
    let bytes = hex::decode(s).map_err(io::Error::other)?;
    Ok(Tag::from(bytes.as_slice()))
}

fn format_from_u8(n: u8) -> BlobFormat {
    if n == 0 {
        BlobFormat::Raw
    } else {
        BlobFormat::HashSeq
    }
}

fn format_to_u8(f: BlobFormat) -> u8 {
    if f == BlobFormat::Raw { 0 } else { 1 }
}

// ---------- JSON ↔ JsValue helpers ----------

fn to_js<T: Serialize>(val: &T) -> io::Result<JsValue> {
    let json = serde_json::to_string(val).map_err(io::Error::other)?;
    js_sys::JSON::parse(&json).map_err(|_| io::Error::other("JSON.parse failed"))
}

fn from_js<T: serde::de::DeserializeOwned>(js: JsValue) -> io::Result<T> {
    let json = js_sys::JSON::stringify(&js)
        .map(String::from)
        .map_err(|_| io::Error::other("JSON.stringify failed"))?;
    serde_json::from_str(&json).map_err(io::Error::other)
}

/// Build a JS object `{ hash: "...", data: Uint8Array }` for chunk storage.
fn make_chunk_value(hash_hex: &str, data: &[u8]) -> JsValue {
    let obj = js_sys::Object::new();
    let arr = js_sys::Uint8Array::from(data);
    let _ = js_sys::Reflect::set(&obj, &"hash".into(), &hash_hex.into());
    let _ = js_sys::Reflect::set(&obj, &"data".into(), &arr.into());
    obj.into()
}

/// Extract the `data` bytes from a `{ hash, data: Uint8Array }` JS value.
fn extract_chunk_data(js: JsValue) -> Option<Vec<u8>> {
    let data_js = js_sys::Reflect::get(&js, &"data".into()).ok()?;
    let arr = js_sys::Uint8Array::try_from(data_js).ok()?;
    Some(arr.to_vec())
}

// ---------- chunk key helpers ----------

fn data_chunk_key(hash_hex: &str, idx: u64) -> String {
    format!("{hash_hex}|{idx:016x}")
}

fn outboard_node_key(hash_hex: &str, node_idx: u64) -> String {
    format!("{hash_hex}|{node_idx:016x}")
}

/// Key range for all records belonging to `hash_hex` in stores that use
/// the `"{hash}|{idx:016x}"` key scheme.  Relies on `}` (0x7D) > `|` (0x7C).
fn hash_key_range(hash_hex: &str) -> io::Result<IdbKeyRange> {
    let lower = JsValue::from_str(&format!("{hash_hex}|"));
    let upper = JsValue::from_str(&format!("{hash_hex}}}"));
    IdbKeyRange::bound_with_lower_open_and_upper_open(&lower, &upper, false, true)
        .map_err(|_| io::Error::other("idb key range failed"))
}

// ---------- IndexedDbBlobDb ----------

/// Owns the `IdbDatabase` handle and provides typed async helpers.
/// `Rc` (not `Arc`) is intentional: WASM is single-threaded.
#[derive(Clone)]
struct IndexedDbBlobDb(Rc<IdbDatabase>);

impl std::fmt::Debug for IndexedDbBlobDb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("IndexedDbBlobDb").finish_non_exhaustive()
    }
}

impl IndexedDbBlobDb {
    async fn open() -> io::Result<Self> {
        let db = open_db(DB_NAME, DB_VERSION).await?;
        Ok(Self(Rc::new(db)))
    }

    // --- readwrite transaction helper ---

    fn rw_tx(&self, stores: &[&str]) -> io::Result<web_sys::IdbTransaction> {
        let names = js_sys::Array::new();
        for s in stores {
            names.push(&JsValue::from_str(s));
        }
        self.0
            .transaction_with_str_sequence_and_mode(&names, IdbTransactionMode::Readwrite)
            .map_err(|_| io::Error::other("idb tx failed"))
    }

    fn ro_tx(&self, store: &str) -> io::Result<web_sys::IdbTransaction> {
        self.0
            .transaction_with_str(store)
            .map_err(|_| io::Error::other("idb ro tx failed"))
    }

    // --- entry operations ---

    #[allow(dead_code)]
    async fn get_entry(&self, hash_hex: &str) -> io::Result<Option<EntryRecord>> {
        let tx = self.ro_tx(STORE_ENTRIES)?;
        let store = tx
            .object_store(STORE_ENTRIES)
            .map_err(|_| io::Error::other("object_store"))?;
        let req = store
            .get(&JsValue::from_str(hash_hex))
            .map_err(|_| io::Error::other("get entry"))?;
        let val = await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("get entry await: {e:?}")))?;
        if val.is_undefined() || val.is_null() {
            return Ok(None);
        }
        Ok(Some(from_js(val)?))
    }

    async fn put_entry(&self, rec: &EntryRecord) -> io::Result<()> {
        let tx = self.rw_tx(&[STORE_ENTRIES])?;
        let store = tx
            .object_store(STORE_ENTRIES)
            .map_err(|_| io::Error::other("object_store"))?;
        let val = to_js(rec)?;
        let key = JsValue::from_str(&rec.hash);
        let req = store
            .put_with_key(&val, &key)
            .map_err(|_| io::Error::other("put entry"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("put entry await: {e:?}")))?;
        Ok(())
    }

    async fn delete_entry(&self, hash_hex: &str) -> io::Result<()> {
        let tx = self.rw_tx(&[STORE_ENTRIES])?;
        let store = tx
            .object_store(STORE_ENTRIES)
            .map_err(|_| io::Error::other("object_store"))?;
        let req = store
            .delete(&JsValue::from_str(hash_hex))
            .map_err(|_| io::Error::other("delete entry"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("delete entry await: {e:?}")))?;
        Ok(())
    }

    async fn list_all_entries(&self) -> io::Result<Vec<EntryRecord>> {
        let tx = self.ro_tx(STORE_ENTRIES)?;
        let store = tx
            .object_store(STORE_ENTRIES)
            .map_err(|_| io::Error::other("object_store"))?;
        let req = store
            .get_all()
            .map_err(|_| io::Error::other("get_all entries"))?;
        let arr_val = await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("get_all entries await: {e:?}")))?;
        let arr = js_sys::Array::from(&arr_val);
        let mut out = Vec::new();
        for item in arr.iter() {
            match from_js::<EntryRecord>(item) {
                Ok(rec) => out.push(rec),
                Err(e) => error!("failed to deserialize entry record: {e}"),
            }
        }
        Ok(out)
    }

    // --- data chunk operations ---

    async fn put_data_chunk(&self, hash_hex: &str, idx: u64, data: &[u8]) -> io::Result<()> {
        let tx = self.rw_tx(&[STORE_DATA_CHUNKS])?;
        let store = tx
            .object_store(STORE_DATA_CHUNKS)
            .map_err(|_| io::Error::other("object_store data_chunks"))?;
        let key = JsValue::from_str(&data_chunk_key(hash_hex, idx));
        let val = make_chunk_value(hash_hex, data);
        let req = store
            .put_with_key(&val, &key)
            .map_err(|_| io::Error::other("put data_chunk"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("put data_chunk await: {e:?}")))?;
        Ok(())
    }

    /// Fetch data chunks whose indices fall within `[idx_start, idx_end_exclusive)`.
    async fn get_data_chunks_range(
        &self,
        hash_hex: &str,
        idx_start: u64,
        idx_end_exclusive: u64,
    ) -> io::Result<Vec<(u64, Vec<u8>)>> {
        if idx_start >= idx_end_exclusive {
            return Ok(vec![]);
        }
        let lower = JsValue::from_str(&data_chunk_key(hash_hex, idx_start));
        let upper = JsValue::from_str(&data_chunk_key(hash_hex, idx_end_exclusive));
        let range = IdbKeyRange::bound_with_lower_open_and_upper_open(&lower, &upper, false, true)
            .map_err(|_| io::Error::other("data_chunks key range"))?;

        let tx = self.ro_tx(STORE_DATA_CHUNKS)?;
        let store = tx
            .object_store(STORE_DATA_CHUNKS)
            .map_err(|_| io::Error::other("object_store data_chunks"))?;

        // fetch keys and values in parallel requests within the same transaction
        let keys_req = store
            .get_all_keys_with_key(&range)
            .map_err(|_| io::Error::other("get_all_keys data_chunks"))?;
        let vals_req = store
            .get_all_with_key(&range)
            .map_err(|_| io::Error::other("get_all data_chunks"))?;

        let keys_arr = js_sys::Array::from(
            &await_request(keys_req)
                .await
                .map_err(|e| io::Error::other(format!("get_all_keys await: {e:?}")))?,
        );
        let vals_arr = js_sys::Array::from(
            &await_request(vals_req)
                .await
                .map_err(|e| io::Error::other(format!("get_all_vals await: {e:?}")))?,
        );

        let chunk_len = IROH_BLOCK_SIZE.bytes() as u64;
        let mut out = Vec::new();
        for i in 0..keys_arr.length() {
            let key_str = String::from(js_sys::JsString::from(keys_arr.get(i)));
            // key format: "{hash_hex}|{idx:016x}"
            let idx = u64::from_str_radix(key_str.splitn(2, '|').nth(1).unwrap_or("0"), 16)
                .unwrap_or(0);
            let data = extract_chunk_data(vals_arr.get(i))
                .ok_or_else(|| io::Error::other("extract chunk data"))?;
            out.push((idx * chunk_len, data));
        }
        Ok(out)
    }

    async fn delete_data_chunks(&self, hash_hex: &str) -> io::Result<()> {
        let range = hash_key_range(hash_hex)?;
        let tx = self.rw_tx(&[STORE_DATA_CHUNKS])?;
        let store = tx
            .object_store(STORE_DATA_CHUNKS)
            .map_err(|_| io::Error::other("object_store data_chunks"))?;
        let req = store
            .delete(&range)
            .map_err(|_| io::Error::other("delete data_chunks range"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("delete data_chunks await: {e:?}")))?;
        Ok(())
    }

    // --- outboard chunk operations ---

    async fn put_outboard_node(&self, hash_hex: &str, node_idx: u64, data: &[u8]) -> io::Result<()> {
        let tx = self.rw_tx(&[STORE_OUTBOARD])?;
        let store = tx
            .object_store(STORE_OUTBOARD)
            .map_err(|_| io::Error::other("object_store outboard"))?;
        let key = JsValue::from_str(&outboard_node_key(hash_hex, node_idx));
        let val = make_chunk_value(hash_hex, data);
        let req = store
            .put_with_key(&val, &key)
            .map_err(|_| io::Error::other("put outboard node"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("put outboard await: {e:?}")))?;
        Ok(())
    }

    /// Returns `(node_idx, data)` pairs for all stored outboard nodes of `hash`.
    async fn get_all_outboard(&self, hash_hex: &str) -> io::Result<Vec<(u64, [u8; 64])>> {
        let range = hash_key_range(hash_hex)?;
        let tx = self.ro_tx(STORE_OUTBOARD)?;
        let store = tx
            .object_store(STORE_OUTBOARD)
            .map_err(|_| io::Error::other("object_store outboard"))?;

        let keys_req = store
            .get_all_keys_with_key(&range)
            .map_err(|_| io::Error::other("get_all_keys outboard"))?;
        let vals_req = store
            .get_all_with_key(&range)
            .map_err(|_| io::Error::other("get_all outboard"))?;

        let keys_arr = js_sys::Array::from(
            &await_request(keys_req)
                .await
                .map_err(|e| io::Error::other(format!("get_all_keys outboard await: {e:?}")))?,
        );
        let vals_arr = js_sys::Array::from(
            &await_request(vals_req)
                .await
                .map_err(|e| io::Error::other(format!("get_all outboard await: {e:?}")))?,
        );

        let mut out = Vec::new();
        for i in 0..keys_arr.length() {
            let key_str = String::from(js_sys::JsString::from(keys_arr.get(i)));
            let node_idx =
                u64::from_str_radix(key_str.splitn(2, '|').nth(1).unwrap_or("0"), 16)
                    .unwrap_or(0);
            let data = extract_chunk_data(vals_arr.get(i))
                .ok_or_else(|| io::Error::other("extract outboard data"))?;
            if data.len() == 64 {
                let mut arr = [0u8; 64];
                arr.copy_from_slice(&data);
                out.push((node_idx, arr));
            }
        }
        Ok(out)
    }

    async fn delete_outboard_chunks(&self, hash_hex: &str) -> io::Result<()> {
        let range = hash_key_range(hash_hex)?;
        let tx = self.rw_tx(&[STORE_OUTBOARD])?;
        let store = tx
            .object_store(STORE_OUTBOARD)
            .map_err(|_| io::Error::other("object_store outboard"))?;
        let req = store
            .delete(&range)
            .map_err(|_| io::Error::other("delete outboard range"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("delete outboard await: {e:?}")))?;
        Ok(())
    }

    // --- tag operations ---

    async fn put_tag(&self, tag_hex: &str, rec: &TagRecord) -> io::Result<()> {
        let tx = self.rw_tx(&[STORE_TAGS])?;
        let store = tx
            .object_store(STORE_TAGS)
            .map_err(|_| io::Error::other("object_store tags"))?;
        let val = to_js(rec)?;
        let key = JsValue::from_str(tag_hex);
        let req = store
            .put_with_key(&val, &key)
            .map_err(|_| io::Error::other("put tag"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("put tag await: {e:?}")))?;
        Ok(())
    }

    async fn delete_tag_idb(&self, tag_hex: &str) -> io::Result<()> {
        let tx = self.rw_tx(&[STORE_TAGS])?;
        let store = tx
            .object_store(STORE_TAGS)
            .map_err(|_| io::Error::other("object_store tags"))?;
        let req = store
            .delete(&JsValue::from_str(tag_hex))
            .map_err(|_| io::Error::other("delete tag"))?;
        await_request(req)
            .await
            .map_err(|e| io::Error::other(format!("delete tag await: {e:?}")))?;
        Ok(())
    }

    async fn list_all_tags_idb(&self) -> io::Result<Vec<(String, TagRecord)>> {
        let tx = self.ro_tx(STORE_TAGS)?;
        let store = tx
            .object_store(STORE_TAGS)
            .map_err(|_| io::Error::other("object_store tags"))?;
        let keys_req = store
            .get_all_keys()
            .map_err(|_| io::Error::other("get_all_keys tags"))?;
        let vals_req = store
            .get_all()
            .map_err(|_| io::Error::other("get_all tags"))?;

        let keys_arr = js_sys::Array::from(
            &await_request(keys_req)
                .await
                .map_err(|e| io::Error::other(format!("get_all_keys tags await: {e:?}")))?,
        );
        let vals_arr = js_sys::Array::from(
            &await_request(vals_req)
                .await
                .map_err(|e| io::Error::other(format!("get_all tags await: {e:?}")))?,
        );

        let mut out = Vec::new();
        for i in 0..keys_arr.length() {
            let key = String::from(js_sys::JsString::from(keys_arr.get(i)));
            match from_js::<TagRecord>(vals_arr.get(i)) {
                Ok(rec) => out.push((key, rec)),
                Err(e) => error!("failed to deserialize tag: {e}"),
            }
        }
        Ok(out)
    }
}

// ---------- in-memory entry state ----------

#[derive(Debug, Clone)]
struct EntrySnapshot {
    size: u64,
    bitfield: Bitfield,
}

impl EntrySnapshot {
    fn empty() -> Self {
        Self {
            size: 0,
            bitfield: Bitfield::empty(),
        }
    }
    fn complete(size: u64) -> Self {
        Self {
            size,
            bitfield: Bitfield::complete(size),
        }
    }
}

#[derive(Clone, Debug)]
struct EntryHandle {
    hash: Hash,
    db: IndexedDbBlobDb,
    tx: watch::Sender<EntrySnapshot>,
}

impl EntryHandle {
    fn new_partial(hash: Hash, db: IndexedDbBlobDb) -> Self {
        let (tx, _) = watch::channel(EntrySnapshot::empty());
        Self { hash, db, tx }
    }

    fn new_from_record(hash: Hash, db: IndexedDbBlobDb, rec: &EntryRecord) -> Self {
        let snap = EntrySnapshot {
            size: rec.size,
            bitfield: rec.bitfield.clone(),
        };
        let (tx, _) = watch::channel(snap);
        Self { hash, db, tx }
    }

    fn bitfield(&self) -> Bitfield {
        self.tx.borrow().bitfield.clone()
    }

    fn subscribe(&self) -> watch::Receiver<EntrySnapshot> {
        self.tx.subscribe()
    }
}

// ---------- sync readers for export (prefetched data) ----------

/// Sync data reader backed by prefetched chunk map.
/// Keys = byte offset of chunk start, values = chunk data.
struct IdbDataReader {
    chunks: BTreeMap<u64, Bytes>,
}

impl ReadBytesAt for IdbDataReader {
    fn read_bytes_at(&self, offset: u64, size: usize) -> io::Result<Bytes> {
        if size == 0 {
            return Ok(Bytes::new());
        }
        let chunk_len = IROH_BLOCK_SIZE.bytes() as u64;
        let end = offset + size as u64;
        // fast path: single-chunk read
        let chunk_start = (offset / chunk_len) * chunk_len;
        if (end - 1) / chunk_len == offset / chunk_len {
            let chunk = self
                .chunks
                .get(&chunk_start)
                .ok_or_else(|| io::Error::other(format!("missing data chunk at {chunk_start}")))?;
            let within = (offset - chunk_start) as usize;
            return Ok(chunk.slice(within..within + size));
        }
        // multi-chunk read
        let mut result = Vec::with_capacity(size);
        let mut pos = offset;
        while pos < end {
            let cs = (pos / chunk_len) * chunk_len;
            let chunk = self
                .chunks
                .get(&cs)
                .ok_or_else(|| io::Error::other(format!("missing data chunk at {cs}")))?;
            let within = (pos - cs) as usize;
            let avail = (chunk.len() - within).min((end - pos) as usize);
            result.extend_from_slice(&chunk[within..within + avail]);
            pos += avail as u64;
        }
        Ok(Bytes::from(result))
    }
}

/// Sync outboard reader backed by prefetched node map (node_idx → 64-byte pair).
struct IdbOutboard {
    hash: blake3::Hash,
    tree: BaoTree,
    nodes: HashMap<u64, [u8; 64]>,
}

impl bao_tree::io::sync::Outboard for IdbOutboard {
    fn root(&self) -> blake3::Hash {
        self.hash
    }

    fn tree(&self) -> BaoTree {
        self.tree
    }

    fn load(&self, node: TreeNode) -> io::Result<Option<(blake3::Hash, blake3::Hash)>> {
        let Some(offset) = self.tree.pre_order_offset(node) else {
            return Ok(None);
        };
        let Some(pair) = self.nodes.get(&offset) else {
            return Err(io::Error::other(format!("missing outboard node {offset}")));
        };
        let left: [u8; 32] = pair[..32].try_into().unwrap();
        let right: [u8; 32] = pair[32..].try_into().unwrap();
        Ok(Some((left.into(), right.into())))
    }
}

// ---------- actor ----------

#[derive(derive_more::From)]
enum TaskResult {
    Unit(()),
    Import(Result<ImportEntry>),
    Scope(Scope),
}

struct Actor {
    commands: tokio::sync::mpsc::Receiver<Command>,
    tasks: JoinSet<TaskResult>,
    db: IndexedDbBlobDb,
    // in-memory metadata (loaded at startup, written through to IDB)
    entries: HashMap<Hash, EntryHandle>,
    tags: BTreeMap<Tag, HashAndFormat>,
    temp_tags: TempTags,
    protected: HashSet<Hash>,
    idle_waiters: Vec<irpc::channel::oneshot::Sender<()>>,
}

impl Actor {
    fn spawn<F, T>(&mut self, f: F)
    where
        F: Future<Output = T> + 'static,
        T: Into<TaskResult>,
    {
        self.tasks.spawn(async move { f.await.into() });
    }

    fn get_or_create_entry(&mut self, hash: Hash) -> EntryHandle {
        let db = self.db.clone();
        self.entries
            .entry(hash)
            .or_insert_with(|| EntryHandle::new_partial(hash, db))
            .clone()
    }

    fn get_entry(&self, hash: &Hash) -> Option<EntryHandle> {
        self.entries.get(hash).cloned()
    }

    async fn handle_command(&mut self, cmd: Command) -> Option<ShutdownMsg> {
        match cmd {
            Command::ImportBao(ImportBaoMsg {
                inner: ImportBaoRequest { hash, size },
                rx: data,
                tx,
                ..
            }) => {
                let entry = self.get_or_create_entry(hash);
                self.spawn(import_bao(entry, size, data, tx));
            }
            Command::WaitIdle(WaitIdleMsg { tx, .. }) => {
                if self.tasks.is_empty() {
                    tx.send(()).await.ok();
                } else {
                    self.idle_waiters.push(tx);
                }
            }
            Command::Observe(ObserveMsg {
                inner: ObserveRequest { hash },
                tx,
                ..
            }) => {
                let entry = self.get_or_create_entry(hash);
                self.spawn(observe(entry, tx));
            }
            Command::ImportBytes(ImportBytesMsg {
                inner:
                    ImportBytesRequest {
                        data,
                        scope,
                        format,
                        ..
                    },
                tx,
                ..
            }) => {
                self.spawn(import_bytes(data, scope, format, tx));
            }
            Command::ImportByteStream(ImportByteStreamMsg { inner, tx, rx, .. }) => {
                self.spawn(import_byte_stream(inner.scope, inner.format, rx, tx));
            }
            Command::ImportPath(cmd) => {
                // not supported on WASM
                self.spawn(import_path(cmd));
            }
            Command::ExportBao(ExportBaoMsg {
                inner: ExportBaoRequest { hash, ranges },
                tx,
                ..
            }) => {
                let entry = self.get_entry(&hash);
                self.spawn(export_bao(entry, ranges, tx));
            }
            Command::ExportPath(cmd) => {
                let entry = self.get_entry(&cmd.hash);
                self.spawn(export_path(entry, cmd));
            }
            Command::DeleteTags(cmd) => {
                let DeleteTagsMsg {
                    inner: DeleteTagsRequest { from, to },
                    tx,
                    ..
                } = cmd;
                let mut deleted = 0u64;
                let db = self.db.clone();
                let mut to_delete = Vec::new();
                self.tags.retain(|tag, _| {
                    if let Some(from) = &from {
                        if tag < from {
                            return true;
                        }
                    }
                    if let Some(to) = &to {
                        if tag >= to {
                            return true;
                        }
                    }
                    to_delete.push(tag.clone());
                    deleted += 1;
                    false
                });
                self.spawn(async move {
                    for tag in to_delete {
                        if let Err(e) = db.delete_tag_idb(&tag_to_hex(&tag)).await {
                            error!("delete tag idb: {e}");
                        }
                    }
                    tx.send(Ok(deleted)).await.ok();
                });
            }
            Command::RenameTag(cmd) => {
                let RenameTagMsg {
                    inner: RenameTagRequest { from, to },
                    tx,
                    ..
                } = cmd;
                let db = self.db.clone();
                let value = match self.tags.remove(&from) {
                    Some(value) => value,
                    None => {
                        tx.send(Err(api::Error::io(
                            io::ErrorKind::NotFound,
                            format!("tag not found: {from:?}"),
                        )))
                        .await
                        .ok();
                        return None;
                    }
                };
                let new_rec = TagRecord {
                    hash: hash_to_hex(&value.hash),
                    format: format_to_u8(value.format),
                };
                self.tags.insert(to.clone(), value);
                self.spawn(async move {
                    db.delete_tag_idb(&tag_to_hex(&from)).await.ok();
                    db.put_tag(&tag_to_hex(&to), &new_rec).await.ok();
                    tx.send(Ok(())).await.ok();
                });
                return None;
            }
            Command::ListTags(cmd) => {
                let ListTagsMsg {
                    inner:
                        ListTagsRequest {
                            from,
                            to,
                            raw,
                            hash_seq,
                        },
                    tx,
                    ..
                } = cmd;
                let tags = self
                    .tags
                    .iter()
                    .filter(|(tag, value)| {
                        if let Some(from) = &from {
                            if tag < &from {
                                return false;
                            }
                        }
                        if let Some(to) = &to {
                            if tag >= &to {
                                return false;
                            }
                        }
                        raw && value.format.is_raw() || hash_seq && value.format.is_hash_seq()
                    })
                    .map(|(tag, value)| TagInfo {
                        name: tag.clone(),
                        hash: value.hash,
                        format: value.format,
                    })
                    .map(Ok);
                tx.send(tags.collect()).await.ok();
            }
            Command::SetTag(SetTagMsg {
                inner: SetTagRequest { name: tag, value },
                tx,
                ..
            }) => {
                let db = self.db.clone();
                let rec = TagRecord {
                    hash: hash_to_hex(&value.hash),
                    format: format_to_u8(value.format),
                };
                self.tags.insert(tag.clone(), value);
                self.spawn(async move {
                    db.put_tag(&tag_to_hex(&tag), &rec).await.ok();
                    tx.send(Ok(())).await.ok();
                });
                return None;
            }
            Command::CreateTag(CreateTagMsg {
                inner: CreateTagRequest { value },
                tx,
                ..
            }) => {
                let db = self.db.clone();
                let tag = Tag::auto(SystemTime::now(), |t| self.tags.contains_key(t));
                let rec = TagRecord {
                    hash: hash_to_hex(&value.hash),
                    format: format_to_u8(value.format),
                };
                self.tags.insert(tag.clone(), value);
                self.spawn(async move {
                    db.put_tag(&tag_to_hex(&tag), &rec).await.ok();
                    tx.send(Ok(tag)).await.ok();
                });
                return None;
            }
            Command::CreateTempTag(cmd) => {
                trace!("{cmd:?}");
                let CreateTempTagMsg { tx, inner, .. } = cmd;
                let mut tt = self.temp_tags.create(inner.scope, inner.value);
                if tx.is_rpc() {
                    tt.leak();
                }
                tx.send(tt).await.ok();
            }
            Command::ListTempTags(cmd) => {
                let tts = self.temp_tags.list();
                cmd.tx.send(tts).await.ok();
            }
            Command::ListBlobs(cmd) => {
                let ListBlobsMsg { tx, .. } = cmd;
                let blobs = self.entries.keys().cloned().collect::<Vec<_>>();
                self.spawn(async move {
                    for blob in blobs {
                        if tx.send(Ok(blob)).await.is_err() {
                            break;
                        }
                    }
                });
            }
            Command::BlobStatus(cmd) => {
                let BlobStatusMsg {
                    inner: BlobStatusRequest { hash },
                    tx,
                    ..
                } = cmd;
                let res = match self.get_entry(&hash) {
                    None => BlobStatus::NotFound,
                    Some(h) => {
                        let bf = h.bitfield();
                        if bf.is_complete() {
                            BlobStatus::Complete { size: bf.size }
                        } else {
                            BlobStatus::Partial {
                                size: bf.validated_size(),
                            }
                        }
                    }
                };
                tx.send(res).await.ok();
            }
            Command::DeleteBlobs(cmd) => {
                let DeleteBlobsMsg {
                    inner: BlobDeleteRequest { hashes, force },
                    tx,
                    ..
                } = cmd;
                let db = self.db.clone();
                let mut to_delete = Vec::new();
                for hash in hashes {
                    if !force && self.protected.contains(&hash) {
                        continue;
                    }
                    self.entries.remove(&hash);
                    to_delete.push(hash);
                }
                self.spawn(async move {
                    for hash in to_delete {
                        let hex = hash_to_hex(&hash);
                        db.delete_entry(&hex).await.ok();
                        db.delete_data_chunks(&hex).await.ok();
                        db.delete_outboard_chunks(&hex).await.ok();
                    }
                    tx.send(Ok(())).await.ok();
                });
            }
            Command::Batch(cmd) => {
                let (id, scope) = self.temp_tags.create_scope();
                self.spawn(handle_batch(cmd, id, scope));
            }
            Command::ClearProtected(cmd) => {
                self.protected.clear();
                cmd.tx.send(Ok(())).await.ok();
            }
            Command::ExportRanges(cmd) => {
                let entry = self.get_entry(&cmd.hash);
                self.spawn(export_ranges(cmd, entry));
            }
            Command::SyncDb(SyncDbMsg { tx, .. }) => {
                tx.send(Ok(())).await.ok();
            }
            Command::Shutdown(cmd) => {
                return Some(cmd);
            }
        }
        None
    }

    fn log_task_result(&self, res: std::result::Result<TaskResult, JoinError>) -> Option<TaskResult> {
        match res {
            Ok(x) => Some(x),
            Err(e) => {
                if e.is_cancelled() {
                    trace!("task cancelled: {e}");
                } else {
                    error!("task failed: {e}");
                }
                None
            }
        }
    }

    async fn finish_import(&mut self, res: Result<ImportEntry>) {
        let import_data = match res {
            Ok(e) => e,
            Err(e) => {
                error!("import failed: {e}");
                return;
            }
        };
        let hash = import_data.outboard.root.into();
        let hex = hash_to_hex(&hash);
        let size = import_data.data.len() as u64;
        let snap = EntrySnapshot::complete(size);
        let entry = self.get_or_create_entry(hash);
        entry.tx.send_replace(snap);

        let rec = EntryRecord {
            hash: hex.clone(),
            complete: true,
            size,
            bitfield: Bitfield::complete(size),
        };
        let db = self.db.clone();
        let data = import_data.data.clone();
        let outboard_data: Bytes = import_data.outboard.data.into();
        let chunk_len = IROH_BLOCK_SIZE.bytes() as u64;
        let tt_tx = import_data.tx;
        let scope = import_data.scope;
        let format = import_data.format;
        let tt = self.temp_tags.create(scope, HashAndFormat { hash, format });
        self.spawn(async move {
            // persist entry record
            db.put_entry(&rec).await.ok();
            // persist data chunks
            for (i, chunk) in data.chunks(chunk_len as usize).enumerate() {
                db.put_data_chunk(&hex, i as u64, chunk).await.ok();
            }
            // persist outboard nodes (each 64 bytes)
            for (i, pair) in outboard_data.chunks(64).enumerate() {
                if pair.len() == 64 {
                    db.put_outboard_node(&hex, i as u64, pair).await.ok();
                }
            }
            tt_tx.send(AddProgressItem::Done(tt)).await.ok();
        });
    }

    pub async fn run(mut self) {
        let shutdown = loop {
            tokio::select! {
                cmd = self.commands.recv() => {
                    let Some(cmd) = cmd else { break None; };
                    if let Some(cmd) = self.handle_command(cmd).await {
                        break Some(cmd);
                    }
                }
                Some(res) = self.tasks.join_next(), if !self.tasks.is_empty() => {
                    let Some(res) = self.log_task_result(res) else { continue; };
                    match res {
                        TaskResult::Import(res) => self.finish_import(res).await,
                        TaskResult::Scope(scope) => self.temp_tags.end_scope(scope),
                        TaskResult::Unit(_) => {}
                    }
                    if self.tasks.is_empty() {
                        for tx in self.idle_waiters.drain(..) {
                            tx.send(()).await.ok();
                        }
                    }
                }
            }
        };
        if let Some(shutdown) = shutdown {
            self.db.0.close();
            shutdown.tx.send(()).await.ok();
        }
    }
}

// ---------- task functions ----------

async fn handle_batch(cmd: BatchMsg, id: Scope, scope: std::sync::Arc<TempTagScope>) -> Scope {
    if let Err(cause) = handle_batch_impl(cmd, id, &scope).await {
        error!("batch failed: {cause}");
    }
    id
}

async fn handle_batch_impl(
    cmd: BatchMsg,
    id: Scope,
    scope: &std::sync::Arc<TempTagScope>,
) -> api::Result<()> {
    let BatchMsg { tx, mut rx, .. } = cmd;
    tx.send(id).await?;
    while let Some(msg) = rx.recv().await? {
        match msg {
            BatchResponse::Drop(msg) => scope.on_drop(&msg),
            BatchResponse::Ping => {}
        }
    }
    Ok(())
}

async fn observe(entry: EntryHandle, tx: mpsc::Sender<Bitfield>) {
    let mut rx = entry.subscribe();
    // send current snapshot first
    if tx.send(rx.borrow_and_update().bitfield.clone()).await.is_err() {
        return;
    }
    loop {
        tokio::select! {
            _ = tx.closed() => break,
            res = rx.changed() => {
                if res.is_err() { break; }
                if tx.send(rx.borrow().bitfield.clone()).await.is_err() { break; }
            }
        }
    }
}

struct ImportEntry {
    scope: Scope,
    format: BlobFormat,
    data: Bytes,
    outboard: PreOrderMemOutboard,
    tx: mpsc::Sender<AddProgressItem>,
}

async fn import_bytes(
    data: Bytes,
    scope: Scope,
    format: BlobFormat,
    tx: mpsc::Sender<AddProgressItem>,
) -> Result<ImportEntry> {
    tx.send(AddProgressItem::Size(data.len() as u64)).await?;
    tx.send(AddProgressItem::CopyDone).await?;
    let outboard = PreOrderMemOutboard::create(&data, IROH_BLOCK_SIZE);
    Ok(ImportEntry {
        data,
        outboard,
        scope,
        format,
        tx,
    })
}

async fn import_byte_stream(
    scope: Scope,
    format: BlobFormat,
    mut rx: mpsc::Receiver<ImportByteStreamUpdate>,
    tx: mpsc::Sender<AddProgressItem>,
) -> Result<ImportEntry> {
    let mut res = Vec::new();
    loop {
        match rx.recv().await {
            Ok(Some(ImportByteStreamUpdate::Bytes(data))) => {
                res.extend_from_slice(&data);
                tx.send(AddProgressItem::CopyProgress(res.len() as u64))
                    .await?;
            }
            Ok(Some(ImportByteStreamUpdate::Done)) => break,
            Ok(None) => {
                return Err(api::Error::io(
                    io::ErrorKind::UnexpectedEof,
                    "byte stream ended unexpectedly",
                )
                .into());
            }
            Err(e) => return Err(e.into()),
        }
    }
    import_bytes(res.into(), scope, format, tx).await
}

async fn import_path(cmd: crate::api::proto::ImportPathMsg) -> Result<ImportEntry> {
    let _ = cmd;
    Err(n0_error::anyerr!("import_path is not supported in the browser"))
}

fn chunk_range(leaf: &Leaf) -> ChunkRanges {
    let start = ChunkNum::chunks(leaf.offset);
    let end = ChunkNum::chunks(leaf.offset + leaf.data.len() as u64);
    (start..end).into()
}

/// Import a BAO-encoded stream, writing chunks directly to IDB.
async fn import_bao(
    entry: EntryHandle,
    size: NonZeroU64,
    mut stream: mpsc::Receiver<BaoContentItem>,
    done_tx: irpc::channel::oneshot::Sender<api::Result<()>>,
) {
    let size_val = size.get();
    let hash_hex = hash_to_hex(&entry.hash);
    let tree = BaoTree::new(size_val, IROH_BLOCK_SIZE);
    let chunk_len = IROH_BLOCK_SIZE.bytes() as u64;

    // initialise size info if not already set
    entry.tx.send_if_modified(|snap| {
        if snap.size == 0 {
            snap.size = size_val;
            true
        } else {
            false
        }
    });

    while let Some(item) = stream.recv().await.unwrap() {
        match item {
            BaoContentItem::Parent(parent) => {
                if let Some(node_idx) = tree.pre_order_offset(parent.node) {
                    let mut pair = [0u8; 64];
                    pair[..32].copy_from_slice(parent.pair.0.as_bytes());
                    pair[32..].copy_from_slice(parent.pair.1.as_bytes());
                    if let Err(e) = entry.db.put_outboard_node(&hash_hex, node_idx, &pair).await {
                        error!("put outboard node: {e}");
                    }
                }
            }
            BaoContentItem::Leaf(leaf) => {
                let chunk_idx = leaf.offset / chunk_len;
                if let Err(e) = entry
                    .db
                    .put_data_chunk(&hash_hex, chunk_idx, &leaf.data)
                    .await
                {
                    error!("put data chunk: {e}");
                }

                let added = Bitfield::new(chunk_range(&leaf), size_val);
                let became_complete = entry.tx.send_if_modified(|snap| {
                    let update = snap.bitfield.update(&added);
                    if update.changed() {
                        snap.size = size_val;
                        true
                    } else {
                        false
                    }
                });
                // after the last chunk, flush entry metadata to IDB
                if became_complete {
                    let snap = entry.tx.borrow().clone();
                    let rec = EntryRecord {
                        hash: hash_hex.clone(),
                        complete: snap.bitfield.is_complete(),
                        size: snap.size,
                        bitfield: snap.bitfield.clone(),
                    };
                    entry.db.put_entry(&rec).await.ok();
                }
            }
        }
    }

    // final metadata flush regardless of whether complete
    let snap = entry.tx.borrow().clone();
    let rec = EntryRecord {
        hash: hash_hex.clone(),
        complete: snap.bitfield.is_complete(),
        size: snap.size,
        bitfield: snap.bitfield,
    };
    entry.db.put_entry(&rec).await.ok();

    done_tx.send(Ok(())).await.ok();
}

async fn export_bao(
    entry: Option<EntryHandle>,
    ranges: ChunkRanges,
    mut sender: mpsc::Sender<EncodedItem>,
) {
    let Some(entry) = entry else {
        let err = EncodeError::Io(io::Error::new(io::ErrorKind::NotFound, "hash not found"));
        sender.send(err.into()).await.ok();
        return;
    };
    if let Err(e) = export_bao_impl(entry, ranges, &mut sender).await {
        sender.send(e.into()).await.ok();
    }
}

async fn export_bao_impl(
    entry: EntryHandle,
    ranges: ChunkRanges,
    sender: &mut mpsc::Sender<EncodedItem>,
) -> std::result::Result<(), EncodeError> {
    let snap = entry.tx.borrow().clone();
    let size = snap.size;
    let hash_hex = hash_to_hex(&entry.hash);
    let hash_blake3: blake3::Hash = entry.hash.into();
    let chunk_len = IROH_BLOCK_SIZE.bytes() as u64;
    let tree = BaoTree::new(size, IROH_BLOCK_SIZE);

    // compute needed data chunk index range
    let (chunk_start, chunk_end) = if ranges == ChunkRanges::all() {
        let n = (size + chunk_len - 1) / chunk_len;
        (0u64, n)
    } else {
        let mut start = u64::MAX;
        let mut end = 0u64;
        for range in ranges.iter() {
            let (lo, hi) = match range {
                RangeSetRange::Range(r) => (r.start.0, r.end.0),
                RangeSetRange::RangeFrom(r) => (
                    r.start.0,
                    (size + chunk_len - 1) / chunk_len,
                ),
            };
            start = start.min(lo);
            end = end.max(hi);
        }
        if start == u64::MAX { (0, 0) } else { (start, end) }
    };

    // fetch data chunks for the needed range
    let raw_chunks = entry
        .db
        .get_data_chunks_range(&hash_hex, chunk_start, chunk_end)
        .await
        .map_err(|e| EncodeError::Io(e))?;
    let chunks: BTreeMap<u64, Bytes> = raw_chunks
        .into_iter()
        .map(|(offset, data)| (offset, Bytes::from(data)))
        .collect();

    // fetch all outboard nodes
    let outboard_nodes = entry
        .db
        .get_all_outboard(&hash_hex)
        .await
        .map_err(|e| EncodeError::Io(e))?;
    let nodes: HashMap<u64, [u8; 64]> = outboard_nodes.into_iter().collect();

    let data_reader = IdbDataReader { chunks };
    let outboard_reader = IdbOutboard {
        hash: hash_blake3,
        tree,
        nodes,
    };
    let tx = BaoTreeSender::new(sender);
    traverse_ranges_validated(data_reader, outboard_reader, &ranges, tx)
        .await
        .ok();
    Ok(())
}

async fn export_ranges(mut cmd: ExportRangesMsg, entry: Option<EntryHandle>) {
    let Some(entry) = entry else {
        let err = io::Error::new(io::ErrorKind::NotFound, "hash not found");
        cmd.tx.send(ExportRangesItem::Error(err.into())).await.ok();
        return;
    };
    if let Err(e) = export_ranges_impl(cmd.inner, &mut cmd.tx, entry).await {
        cmd.tx
            .send(ExportRangesItem::Error(e.into()))
            .await
            .ok();
    }
}

async fn export_ranges_impl(
    cmd: ExportRangesRequest,
    tx: &mut mpsc::Sender<ExportRangesItem>,
    entry: EntryHandle,
) -> io::Result<()> {
    let ExportRangesRequest { ranges, hash } = cmd;
    let snap = entry.tx.borrow().clone();
    let bitfield = snap.bitfield;
    let size = snap.size;
    let hash_hex = hash_to_hex(&hash);
    let chunk_len = IROH_BLOCK_SIZE.bytes() as u64;

    for range in ranges.iter() {
        let range = match range {
            RangeSetRange::Range(range) => size.min(*range.start)..size.min(*range.end),
            RangeSetRange::RangeFrom(range) => size.min(*range.start)..size,
        };
        let requested = ChunkRanges::bytes(range.start..range.end);
        if !bitfield.ranges.is_superset(&requested) {
            return Err(io::Error::other(format!(
                "missing range: {requested:?}, present: {bitfield:?}",
            )));
        }

        let chunk_start = range.start / chunk_len;
        let chunk_end = (range.end + chunk_len - 1) / chunk_len;
        let chunks = entry
            .db
            .get_data_chunks_range(&hash_hex, chunk_start, chunk_end)
            .await?;
        let chunk_map: BTreeMap<u64, Bytes> = chunks
            .into_iter()
            .map(|(off, d)| (off, Bytes::from(d)))
            .collect();
        let data = IdbDataReader { chunks: chunk_map };

        let bs = 1024u64;
        let mut offset = range.start;
        loop {
            let end_pos = (offset + bs).min(range.end);
            let sz = (end_pos - offset) as usize;
            tx.send(
                Leaf {
                    offset,
                    data: data.read_bytes_at(offset, sz)?,
                }
                .into(),
            )
            .await
            .map_err(|_| io::Error::other("send failed"))?;
            offset = end_pos;
            if offset >= range.end {
                break;
            }
        }
    }
    Ok(())
}

async fn export_path(entry: Option<EntryHandle>, cmd: crate::api::proto::ExportPathMsg) {
    let crate::api::proto::ExportPathMsg { inner: _, tx, .. } = cmd;
    let _ = entry; // not supported on WASM
    tx.send(ExportProgressItem::Error(api::Error::io(
        io::ErrorKind::Unsupported,
        "export_path not supported on WASM",
    )))
    .await
    .ok();
}

// ---------- public API ----------

/// Options for constructing an [`IndexedDbStore`].
#[derive(Debug, Default)]
pub struct Options {
    pub gc_config: Option<crate::store::gc::GcConfig>,
}

/// WASM-only blob store backed by IndexedDB.
///
/// Data persists across page reloads until explicit deletion or GC.
/// Call `crate::store::gc::gc_run_once` periodically (on page load and after
/// transfers) to reclaim unreferenced blobs.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct IndexedDbStore {
    client: ApiClient,
}

impl From<IndexedDbStore> for crate::api::Store {
    fn from(value: IndexedDbStore) -> Self {
        crate::api::Store::from_sender(value.client)
    }
}

impl AsRef<crate::api::Store> for IndexedDbStore {
    fn as_ref(&self) -> &crate::api::Store {
        crate::api::Store::ref_from_sender(&self.client)
    }
}

impl Deref for IndexedDbStore {
    type Target = crate::api::Store;

    fn deref(&self) -> &Self::Target {
        crate::api::Store::ref_from_sender(&self.client)
    }
}

impl IndexedDbStore {
    pub fn from_sender(client: ApiClient) -> Self {
        Self { client }
    }

    /// Open (or create) the IndexedDB store and start the background actor.
    pub async fn open() -> io::Result<Self> {
        Self::open_with_opts(Options::default()).await
    }

    pub async fn open_with_opts(opts: Options) -> io::Result<Self> {
        let db = IndexedDbBlobDb::open().await?;

        // load persisted state at startup
        let entry_records = db.list_all_entries().await?;
        let tag_records = db.list_all_tags_idb().await?;

        let mut entries: HashMap<Hash, EntryHandle> = HashMap::new();
        for rec in &entry_records {
            match hex_to_hash(&rec.hash) {
                Ok(hash) => {
                    let handle = EntryHandle::new_from_record(hash, db.clone(), rec);
                    entries.insert(hash, handle);
                }
                Err(e) => error!("bad entry hash in idb: {e}"),
            }
        }

        let mut tags: BTreeMap<Tag, HashAndFormat> = BTreeMap::new();
        for (hex_key, rec) in &tag_records {
            match (hex_to_tag(hex_key), hex_to_hash(&rec.hash)) {
                (Ok(tag), Ok(hash)) => {
                    tags.insert(tag, HashAndFormat {
                        hash,
                        format: format_from_u8(rec.format),
                    });
                }
                (Err(e), _) | (_, Err(e)) => {
                    error!("bad tag record in idb: {e}");
                }
            }
        }

        let (sender, receiver) = tokio::sync::mpsc::channel(32);
        n0_future::task::spawn(
            Actor {
                commands: receiver,
                tasks: JoinSet::new(),
                db: db.clone(),
                entries,
                tags,
                temp_tags: Default::default(),
                protected: Default::default(),
                idle_waiters: Default::default(),
            }
            .run(),
        );

        let store = Self::from_sender(sender.into());
        if let Some(gc_config) = opts.gc_config {
            n0_future::task::spawn(crate::store::gc::run_gc(
                store.deref().clone(),
                gc_config,
            ));
        }

        info!("indexeddb store opened: {} entries, {} tags", entry_records.len(), tag_records.len());
        Ok(store)
    }
}
