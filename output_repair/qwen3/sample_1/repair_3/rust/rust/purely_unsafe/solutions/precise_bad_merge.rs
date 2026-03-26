#![feature(stmt_expr_attributes)]

fn main() {
    unsafe {
        #[verus::internal(verifast::requires(true))]
        #[verus::internal(verifast::ensures(true))]
        {
            let _x = 0;
            let _y = 0;
            std::hint::unreachable_unchecked();
        }
    }
}