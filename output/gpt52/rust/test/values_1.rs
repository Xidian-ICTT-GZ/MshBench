use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

/*@

predicate nodes(?n, ?vs) =
    n == 0 ?
        vs == nil
    :
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate stack(?s, ?vs) =
    (*s).head |-> ?h &*& nodes(h, vs);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(result != 0 &*& malloc_block_Stack(result) &*& stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ assume(stack != 0);
        //@ close malloc_block_Stack(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0, nil);
        //@ close stack(stack, nil);

        stack
    }

    #[requires(stack(stack, ?vs) &*& malloc_block_Stack(stack))]
    #[ensures(stack(stack, cons(value, vs)) &*& malloc_block_Stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ assume(n != 0);
        //@ close malloc_block_Node(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, cons(value, vs));
        //@ close stack(stack, cons(value, vs));
    }

    #[requires(malloc_block_Stack(stack) &*& stack(stack, ?vs))]
    #[ensures(nodes(?h, vs) &*& (*stack).head |-> h)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, ?vs0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
        //@ open malloc_block_Stack(stack);
    }
}