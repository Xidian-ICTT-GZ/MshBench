predicate int_ref(int *p; int v) = p->v;

fn main()
    requires true
    ensures true
{
    unsafe {
        let mut x: int = 0;
        let mut y: int = 0;
        // Since x and y are local stack variables, no explicit heap ownership needed.
        // The next call is unreachable, so no further spec needed.
        std::hint::unreachable_unchecked();
    }
}