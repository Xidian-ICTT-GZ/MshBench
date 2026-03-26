#![feature(stmt_expr_attributes)]

fn main() {
    unsafe {
        #[requires(true)]
        #[ensures(true)]
        {
            let _x = 0;
            let _y = 0;
            std::hint::unreachable_unchecked();
        }
    }
}