#![feature(stmt_expr_attributes)]
extern crate verifast;

use verifast::prelude::*;

fn main() {
    unsafe {
        let _x = 0;
        let _y = 0;
        std::hint::unreachable_unchecked();
    }
}