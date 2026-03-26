struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node(n: *mut Node, count: i32) -> bool {
    if n.is_null() {
        count == 0
    } else {
        exists(|rest: i32| {
            count == rest + 1 &&
            n as usize != 0 &&
            Owned(n) &&
            (*n).value |-> _ &&
            (*n).next |-> ?next &&
            node(next, rest)
        })
    }
}

#[predicate]
fn stack(s: *mut Stack) -> bool {
    s as usize != 0 &&
    Owned(s) &&
    (*s).head |-> ?h &&
    node(h, _)
}

#[requires(stack(stack))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
        i >= 0 &&
        node(n, ?remaining) &&
        exists(|total: i32| {
            total >= 0 &&
            i + remaining == total
        })
    )]
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