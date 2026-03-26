struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn nodes(n: *mut Node, count: i32) -> bool {
    if n.is_null() {
        count == 0
    } else {
        exists!(#lifetime; let next = (*n).next; nodes(next, count - 1))
    }
}

#[predicate]
fn stack(stack: *mut Stack) -> bool {
    exists!(#lifetime; let head = (*stack).head; nodes(head, ?count))
}

#[requires(stack(stack))]
#[ensures(stack(stack) && result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(nodes(n, ?cnt) && i >= 0 && i + cnt >= 0)]
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}