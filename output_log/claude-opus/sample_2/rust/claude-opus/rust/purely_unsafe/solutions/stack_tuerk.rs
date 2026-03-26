struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Node(node: *mut Node; next: *mut Node, value: i32) =
    (*node).next |-> next &*& (*node).value |-> value;

predicate Nodes(node: *mut Node; count: i32) =
    node == std::ptr::null_mut() ?
        count == 0
    :
        count > 0 &*&
        Node(node, ?next, ?value) &*&
        Nodes(next, count - 1);

predicate Stack(stack: *mut Stack; count: i32) =
    (*stack).head |-> ?head &*&
    Nodes(head, count);

#[requires(Stack(stack, ?count))]
#[ensures(Stack(stack, count) &*& result == count)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(Nodes(n, count - i) &*& i >= 0 &*& i <= count)]
    loop {
        if n.is_null() {
            break;
        }

        open Nodes(n, count - i);
        open Node(n, ?next, ?value);
        close Node(n, next, value);
        close Nodes(next, count - i - 1);

        n = (*n).next;
        i += 1;
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}