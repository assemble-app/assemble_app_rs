use chrono;
pub use chrono::{DateTime, FixedOffset};
use serde;
use serde::de::DeserializeOwned;
pub use serde::{Deserialize, Serialize};
use std::collections::HashMap;
pub use wapc_guest::prelude;
pub use wapc_guest::prelude::{host_call};

#[macro_export]
macro_rules! register_view {
    ($n:ident, $t:ident) => {{
        crate::prelude::register_function(
            &["view-start-", stringify!($n)].join("")[..],
            |b: &[u8]| {
                let params = crate::deserialize(b)?;
                let s = $t::start(params)?;
                serialize(&s)
            },
        );
        crate::prelude::register_function(
            &["view-local-event-", stringify!($n)].join("")[..],
            |b: &[u8]| {
                let (state, name, payload): (&[u8], &str, &[u8]) = crate::deserialize(b)?;
                let mut s: $t = crate::deserialize(state)?;
                s.local_event(name, payload)?;
                serialize(&s)
            },
        );
        crate::prelude::register_function(
            &["view-pubsub-event-", stringify!($n)].join("")[..],
            |b: &[u8]| {
                let (state, topic, name, payload): (&[u8], &str, &str, &[u8]) =
                    crate::deserialize(b)?;
                let mut s: $t = crate::deserialize(state)?;
                s.pubsub_event(topic, name, payload)?;
                serialize(&s)
            },
        );
        crate::prelude::register_function(
            &["view-presence-event-", stringify!($n)].join("")[..],
            |b: &[u8]| {
                let (state, topic, name, payload): (&[u8], &str, &str, &[u8]) =
                    crate::deserialize(b)?;
                let mut s: $t = crate::deserialize(state)?;
                s.presence_event(topic, name, payload)?;
                serialize(&s)
            },
        );
        crate::prelude::register_function(
            &["view-render-", stringify!($n)].join("")[..],
            |b: &[u8]| {
                let s: $t = crate::deserialize(b)?;
                let html = s.render()?;
                Ok(html.into_bytes())
            },
        );
    }};
}
#[macro_export]
macro_rules! register_root_view {
    ($t:ident) => {{
        crate::prelude::register_function(&"view-start-", |b: &[u8]| {
            let params = crate::deserialize(b)?;
            let s = $t::start(params)?;
            serialize(&s)
        });
        crate::prelude::register_function(&"view-local-event-", |b: &[u8]| {
            let (state, name, payload): (&[u8], &str, &[u8]) = crate::deserialize(b)?;
            let mut s: $t = crate::deserialize(state)?;
            s.local_event(name, payload)?;
            serialize(&s)
        });
        crate::prelude::register_function(&"view-pubsub-event", |b: &[u8]| {
            let (state, topic, name, payload): (&[u8], &str, &str, &[u8]) = crate::deserialize(b)?;
            let mut s: $t = crate::deserialize(state)?;
            s.pubsub_event(topic, name, payload)?;
            serialize(&s)
        });
        crate::prelude::register_function(&"view-presence-event", |b: &[u8]| {
            let (state, topic, name, payload): (&[u8], &str, &str, &[u8]) = crate::deserialize(b)?;
            let mut s: $t = crate::deserialize(state)?;
            s.presence_event(topic, name, payload)?;
            serialize(&s)
        });
        crate::prelude::register_function(&"view-render-", |b: &[u8]| {
            let s: $t = crate::deserialize(b)?;
            let html = s.render()?;
            Ok(html.into_bytes())
        });
    }};
}
#[macro_export]
macro_rules! register_call {
    ($n:ident, $f:ident) => {{
        crate::prelude::register_function(&["call-", stringify!($n)].join("")[..], |b: &[u8]| {
            run_function(b, $f)
        });
    }};
}
#[macro_export]
macro_rules! assemble_init {
    ($f:block) => {
        #[no_mangle]
        pub extern "C" fn wapc_init() {
            std::panic::set_hook(Box::new(hook));
            $f
        }
    };
}

pub fn hook(info: &std::panic::PanicInfo) {
    let msg = info.to_string();
    crate::console_log(&msg[..]);
}

pub type Html = String;
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Sync + Send>>;

pub trait View: Sync + Send {
    fn start(params: HashMap<String, String>) -> Result<Self>
    where
        Self: Sized;
    fn local_event(&mut self, _msg: &str, _body: &[u8]) -> Result<()> {
        Ok(())
    }
    fn pubsub_event(&mut self, _topic: &str, _msg: &str, _body: &[u8]) -> Result<()> {
        Ok(())
    }
    fn presence_event(&mut self, _topic: &str, _diff: &PresenceDiffRaw) -> Result<()> {
        Ok(())
    }
    fn render(&self) -> Result<Html>;
}

pub fn serialize<T: ?Sized>(val: &T) -> Result<Vec<u8>>
where
    T: Serialize,
{
    match rmp_serde::to_vec_named(val) {
        Ok(v) => Ok(v),
        Err(v) => Err(Box::new(v)),
    }
}

pub fn deserialize<'a, R: ?Sized, T>(rd: &'a R) -> Result<T>
where
    R: AsRef<[u8]>,
    T: Deserialize<'a>,
{
    match rmp_serde::from_read_ref(rd) {
        Ok(v) => Ok(v),
        Err(v) => Err(Box::new(v)),
    }
}

pub fn run_function<T, R>(
    b: &[u8],
    f: fn(Option<T>) -> std::result::Result<Box<R>, Box<dyn std::error::Error + Sync + Send>>,
) -> wapc_guest::prelude::CallResult
where
    T: DeserializeOwned,
    R: Serialize + ?Sized,
{
    if b.len() == 0 {
        match rmp_serde::to_vec(&f(None)?) {
            Ok(v) => Ok(v),
            Err(v) => Err(Box::new(v)),
        }
    } else {
        match rmp_serde::from_read_ref(&b) {
            Ok(input) => match rmp_serde::to_vec(&f(Some(input))?) {
                Ok(v) => Ok(v),
                Err(v) => Err(Box::new(v)),
            },
            Err(v) => Err(Box::new(v)),
        }
    }
}

#[derive(Deserialize, Serialize, Clone)]
pub struct User {
    id: String,
    username: String,
}

#[derive(Deserialize, Serialize, Clone)]
pub struct ScanOpts {
    limit: u32,
    reverse: bool,
    start_key: Option<String>,
}

#[derive(Deserialize, Serialize, Clone)]
pub struct PresenceDiffRaw {
    joins: HashMap<String, Vec<Vec<u8>>>,
    leaves: HashMap<String, Vec<Vec<u8>>>,
}

#[derive(Deserialize, Serialize)]
pub struct PresenceDiff<T> {
    joins: HashMap<String, Vec<T>>,
    leaves: HashMap<String, Vec<T>>,
}


impl Default for ScanOpts {
    fn default() -> ScanOpts {
        ScanOpts {
            limit: 100,
            reverse: false,
            start_key: None,
        }
    }
}

impl ScanOpts {
    pub fn limit(&self, limit: u32) -> ScanOpts {
        let mut m = self.clone();
        m.limit = limit;
        m
    }
    pub fn reverse(&self, reverse: bool) -> ScanOpts {
        let mut m = self.clone();
        m.reverse = reverse;
        m
    }
    pub fn start_key(&self, start_key: String) -> ScanOpts {
        let mut m = self.clone();
        m.start_key = Some(start_key);
        m
    }
}

pub fn utc_now() -> Result<DateTime<FixedOffset>> {
    let res = host_call("v1", "time", "UTC_NOW", &serialize(&())?)?;
    let st: &str = deserialize(&res)?;
    match DateTime::parse_from_rfc3339(st) {
        Ok(v) => Ok(v),
        Err(e) => Err(e.into()),
    }
}

pub fn console_log(s: &str) -> Result<()> {
    let res = host_call("v1", "console", "LOG", &serialize(&(s,))?)?;
    deserialize(&res)
}

pub fn current_user() -> Result<Option<User>> {
    let res = host_call("v1", "user", "USER", &serialize(&())?)?;
    deserialize(&res)
}

pub fn kv_get<T>(b: &str, k: &str) -> Result<Option<T>>
where
    T: DeserializeOwned,
{
    let res = host_call("v1", "kv", "GET", &serialize(&(b, k))?)?;
    deserialize(&res)
}

pub fn kv_scan<T>(b: &str, opts: &ScanOpts) -> Result<Vec<(String, T)>>
where
    T: DeserializeOwned,
{
    let res = host_call("v1", "kv", "SCAN", &serialize(&(b, opts))?)?;
    deserialize(&res)
}

pub fn kv_set<T>(b: &str, k: &str, obj: &T) -> Result<()>
where
    T: Serialize,
{
    host_call("v1", "kv", "SET", &serialize(&(b, k, obj))?)?;
    Ok(())
}

pub fn kv_patch<T>(b: &str, k: &str, obj: &T) -> Result<()>
where
    T: Serialize,
{
    host_call("v1", "kv", "PATCH", &serialize(&(b, k, obj))?)?;
    Ok(())
}

pub fn kv_delete(b: &str, k: &str) -> Result<()> {
    host_call("v1", "kv", "DELETE", &serialize(&(b, k))?)?;
    Ok(())
}

pub fn kv_patch_delete_fields(b: &str, k: &str, v: Vec<String>) -> Result<()> {
    host_call("v1", "kv", "PATCH_DEL", &serialize(&(b, k, v))?)?;
    Ok(())
}

pub fn pubsub_subscribe(k: &str) -> Result<()> {
    let res = host_call("v1", "pubsub", "SUB", &serialize(k)?)?;
    deserialize(&res)
}

pub fn pubsub_unsubscribe(k: &str) -> Result<()> {
    let res = host_call("v1", "pubsub", "UNSUB", &serialize(&(k,))?)?;
    deserialize(&res)
}

pub fn pubsub_publish<T>(k: &str, event: &str, v: &T) -> Result<()>
where
    T: Serialize,
{
    let s: serde_bytes::ByteBuf = serde_bytes::ByteBuf::from(serialize(v)?);
    let res = host_call("v1", "pubsub", "PUB", &serialize(&(k, event, s))?)?;
    deserialize(&res)
}

pub fn pubsub_publish_from<T>(k: &str, event: &str, v: &T) -> Result<()>
where
    T: Serialize,
{
    let s: serde_bytes::ByteBuf = serde_bytes::ByteBuf::from(serialize(v)?);
    let res = host_call("v1", "pubsub", "PUB_FROM", &serialize(&(k, event, s))?)?;
    deserialize(&res)
}

pub fn presence_track<T>(topic: &str, key: &str, v: &T) -> Result<()>
where
    T: Serialize,
{
    let s: serde_bytes::ByteBuf = serde_bytes::ByteBuf::from(serialize(v)?);
    let res = host_call("v1", "presence", "TRACK", &serialize(&(topic, key, s))?)?;
    deserialize(&res)
}

pub fn presence_list<T>(topic: &str) -> Result<HashMap<String, Vec<T>>>
where
    T: DeserializeOwned,
{
    let res = host_call("v1", "presence", "LIST", &serialize(&(topic,))?[..])?;
    
    let map = deserialize::<_, HashMap<String, Vec<serde_bytes::ByteBuf>>>(&res)?
        .into_iter()
        .map(|(k, x)| (k, x.into_iter().flat_map(|e| deserialize(&e)).collect()))
        .collect();

    Ok(map)
}
pub fn presence_deserialize_diff<T>(diff: PresenceDiffRaw) -> Result<PresenceDiff<T>>
where
    T: DeserializeOwned,
{
    let joins =
        diff.joins
        .into_iter()
        .map(|(k, x)| (k, x.into_iter().flat_map(|e| deserialize(&e)).collect()))
        .collect();
    let leaves =
        diff.leaves
        .into_iter()
        .map(|(k, x)| (k, x.into_iter().flat_map(|e| deserialize(&e)).collect()))
        .collect();

    Ok(PresenceDiff{joins: joins, leaves: leaves})
}

pub fn local_send<T>(event: &str, v: &T) -> Result<()>
where
    T: Serialize,
{
    local_send_timeout(event, v, 0)
}

pub fn local_send_timeout<T>(event: &str, v: &T, timeout_ms: u32) -> Result<()>
where
    T: Serialize,
{
    let s: serde_bytes::ByteBuf = serde_bytes::ByteBuf::from(serialize(v)?);
    let res = host_call("v1", "local", "SEND", &serialize(&(event, s, timeout_ms))?)?;
    deserialize(&res)
}

