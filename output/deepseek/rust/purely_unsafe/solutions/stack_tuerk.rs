struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node, value: i32, next: *mut Node) -> bool {
    struct Node { next: *mut Node, value: i32 }(n) &&
    (*n).value == value &&
    (*n).next == next
}

#[predicate]
fn nodes(n: *mut Node) -> bool {
    n.is_null() ? true :
    exists!(value: i32, next: *mut Node |
        node(n, value, next) &&
        nodes(next)
    )
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    struct Stack { head: *mut Node }(s) &&
    exists!(head: *mut Node |
        (*s).head == head &&
        nodes(head)
    )
}

#[requires(stack(stack))]
#[ensures(result >= 0)]
#[ensures(stack(stack))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    #[invariant(stack(stack))]
    #[invariant(exists!(head: *mut Node | (*stack).head == head && nodes(head)))]
    #[invariant(n.is_null() ? true : nodes(n))]
    #[invariant(i >= 0)]
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        if n.is_null() {
            break;
        }
        #[assert(nodes(n))]
        #[assert(exists!(value: i32, next: *mut Node | node(n, value, next) && nodes(next)))]
        n = (*n).next;
        i += 1;
    }

    i
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}