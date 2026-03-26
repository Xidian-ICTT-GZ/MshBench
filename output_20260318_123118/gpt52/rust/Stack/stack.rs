use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes_list(ptr: *mut Node, count: i32) =
    ptr == 0 ?
        count == 0
    :
        ptr->next |-> ?nxt &*& ptr->value |-> ?v &*& nodes_list(nxt, count - 1) &*& count > 0;

predicate stack(ptr: *mut Stack, count: i32) =
    ptr->head |-> ?h &*& nodes_list(h, count);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes_list(0, 0);
        //@ close stack(stack, 0);

        stack
    }

    #[requires(stack(stack, ?c))]
    #[ensures(stack(stack, c + 1))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, c);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;

        //@ close nodes_list(n, c + 1);
        //@ close stack(stack, c + 1);
    }

    #[requires(stack(stack, ?c) &*& c > 0)]
    #[ensures(stack(stack, c - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, c);
        let head = (*stack).head;
        //@ open nodes_list(head, c);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes_list((*head).next, c - 1);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, c - 1);

        result
    }

    #[requires(stack(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, 0);
        //@ open nodes_list(0, 0);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}