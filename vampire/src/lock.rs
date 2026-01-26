use std::sync::{Mutex, MutexGuard};

pub struct Ctx {
    pub free_var: u32,
}

static GLOBAL_LOCK: Mutex<Ctx> = Mutex::new(Ctx { free_var: 0 });

pub fn synced<R, F: FnOnce(&mut MutexGuard<Ctx>) -> R>(f: F) -> R {
    let mut handle = GLOBAL_LOCK.lock().unwrap();
    let res = f(&mut handle);
    drop(handle);
    res
}
