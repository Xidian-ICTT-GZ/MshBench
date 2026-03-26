use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node(n: *mut Node) =
    n != 0 &*&
    struct_Node_next(n, ?next) &*&
    struct_Node_value(n, ?value);

pred stack(s: *mut Stack) =
    s != 0 &*&
    struct_Stack_head(s, ?head);
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close_struct(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack);
    //@ ens stack(stack);
    {
        //@ open stack(stack);

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close_struct(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n);
        //@ open node(n);
        (*stack).head = n;

        //@ close stack(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open_struct(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}