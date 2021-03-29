use std::io::stdin;
use super::std_ext::KtStd;

pub fn wait_enter() {
    loop {
        if String::new() == String::new().also_mut(|s| stdin().read_line(s)).trim() {
            break
        }
    }
}