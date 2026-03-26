use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(struct node_ptr: *mut Node; int value, struct next_ptr: *mut Node) =
    node_ptr |-> Node { next: next_ptr, value: value };

predicate nodes(struct start: *mut Node, list: list<int>) =
    match list {
        Nil => start == std::ptr::null_mut(),
        Cons(h, t) => 
            exists (next: *mut Node)
                node(start; h, next) &*& nodes(next, t)
    };

predicate stack(struct s: *mut Stack; list<int> contents) =
    s |-> Stack { head: ?head } &*& nodes(head, contents);

impl Stack {

    #[requires(true)]
    #[ensures(stack(res, Nil))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        stack
    }

    #[requires(stack(stack, ?contents))]
    #[ensures(stack(stack, Cons(value, contents_old)))]
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

    #[requires(stack(stack, Cons(?x, ?xs)))]
    #[ensures(stack(stack, xs))]
    #[ensures(result == x)]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack, Nil))]
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
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}