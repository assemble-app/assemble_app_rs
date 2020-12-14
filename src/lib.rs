pub use wapc_guest::prelude;
pub use wapc_guest::prelude::{console_log, host_call};
use serde;

use rmp_serde as rmps;

pub use serde::{Deserialize, Serialize};
use serde::de::DeserializeOwned;
use std::fmt;
use std::collections::HashMap;


#[macro_export]
macro_rules! register_view {
    ($n:ident, $t:ident) => {{
        crate::prelude::register_function(&["view-start-", stringify!($n)].join("")[..], |b: &[u8]| {
            let params = crate::deserialize(b)?;
            let s = $t::start(params)?;
            serialize(&s)
        });
        crate::prelude::register_function(&["view-event-", stringify!($n)].join("")[..], |b: &[u8]| {
            let (state, name, payload): (&[u8], &str, &[u8]) = crate::deserialize(b)?;
            let mut s: $t = crate::deserialize(state)?;
            s.event(name, payload)?;
            serialize(&s)
        });
        crate::prelude::register_function(&["view-render-", stringify!($n)].join("")[..], |b: &[u8]| {
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
    let mut msg = info.to_string();
    wapc_guest::prelude::console_log(&msg[..]);
}


pub type Html = String;
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error + Sync + Send>>;

pub trait View: Sync + Send {
    fn start(params: HashMap<String, String>) -> Result<Self> where Self: Sized;
    fn event(&mut self, msg: &str, body: &[u8]) -> Result<()>;
    fn render(&self) -> Result<Html>;
}

pub fn serialize<T: ?Sized>(val: &T) -> Result<Vec<u8>> where
    T: Serialize {
        match rmp_serde::to_vec(val) {
            Ok(v) => Ok(v),
            Err(v) => Err(Box::new(v)),
        }
}

pub fn deserialize<'a, R: ?Sized, T>(rd: &'a R) -> Result<T> where
    R: AsRef<[u8]>,
    T: Deserialize<'a> {
        match rmp_serde::from_read_ref(rd) {
            Ok(v) => Ok(v),
            Err(v) => Err(Box::new(v)),
        }
}

pub fn run_function<T, R>(b: &[u8], f: fn(&Option<T>) -> std::result::Result<Box<R>, Box<dyn std::error::Error + Sync + Send>>) -> wapc_guest::prelude::CallResult where T: DeserializeOwned, R: Serialize + ?Sized {
    if b.len() == 0 {
        match rmp_serde::to_vec(&f(&None)?) {
            Ok(v) => Ok(v),
            Err(v) => Err(Box::new(v)),
        }
    } else {
        match rmp_serde::from_read_ref(&b){
            Ok(input) => {
                match rmp_serde::to_vec(&f(&Some(input))?) {
                    Ok(v) => Ok(v),
                    Err(v) => Err(Box::new(v)),
                }
            }
            Err(v) => Err(Box::new(v)),
        }
    }

}