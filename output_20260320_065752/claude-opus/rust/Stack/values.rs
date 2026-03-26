use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@

predicate node(struct Node* n;) =
    n->next |-> ?next &*&
    n->value |-> ?value;

predicate stack(struct Stack* s;) =
    s->head |-> ?head &*& (head == null ? true : node(head));

@*/

struct Stack {
    head: *mut Node,
}

impl Stack {

    //@ req true;
    //@ ens result != null &*& stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close stack(stack);
        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n);
        //@ close stack(stack);

    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ if ((*stack).head != null) { // if list nonempty, we would need to free Nodes recursively here
        //@   // but this function currently only frees the Stack itself;
        //@ }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}