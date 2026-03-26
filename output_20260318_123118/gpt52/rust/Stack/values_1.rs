use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
next: *mut Node,
value: i32,
}
struct Stack {
head: *mut Node,
}

/*@

predicate node(p: *mut Node, next: *mut Node, v: i32) =
    p != 0 &*&
    (*p).next |-> next &*&
    (*p).value |-> v;

predicate nodes(p: *mut Node) =
    p == 0 ?
        emp
    :
        (*p).next |-> ?nxt &*& (*p).value |-> ?v &*& malloc_block_Node(p) &*& nodes(nxt);

predicate stack(s: *mut Stack) =
    s != 0 &*&
    (*s).head |-> ?h &*& malloc_block_Stack(s) &*& nodes(h);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close malloc_block_Stack(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);
        stack
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close malloc_block_Node(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}