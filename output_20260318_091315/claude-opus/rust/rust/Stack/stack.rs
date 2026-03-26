use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(*n: *mut Node, list: list<int>) = 
    n != std::ptr::null_mut() &*&
    n->next |-> ?next &*& n->value |-> ?v &*&
    nodes(next, ?rest) &*& list == cons(v, rest)
    || (n == std::ptr::null_mut() &*& list == nil);

predicate nodes(nil: *mut Node, list: list<int>) = nil == std::ptr::null_mut() &*& list == nil;

predicate stack(*s: *mut Stack, list: list<int>) = 
    s != std::ptr::null_mut() &*& s->head |-> ?head &*& nodes(head, list);

impl Stack {

    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, cons(value, list)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, cons(?v, ?rest)))]
    #[ensures(stack(stack, rest))]
    #[ensures(result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
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