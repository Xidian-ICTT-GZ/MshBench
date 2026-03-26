fn main() {
    unsafe {
        let _x = 0;
        let _y = 0;

        std::hint::unreachable_unchecked();
    }
}