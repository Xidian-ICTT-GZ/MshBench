use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate node(*mut Node n; i32 value, *mut Node next) =
    n != null &*&
    struct_Node_padding(n) &*&
    struct_Node_next(n, next) &*&
    struct_Node_value(n, value);

predicate nodes(*mut Node head; list<i32> values) =
    match values {
        nil => head == null,
        cons(h, t) => exists(?next) &*& node(head, h, next) &*& nodes(next, t)
    };

predicate stack(*mut Stack s; list<i32> values) =
    s != null &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, ?head) &*&
    nodes(head, values);

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires *n |-> ?head &*& nodes(head, ?vs) &*& foreach(vs, p),
    ensures *n |-> ?new_head &*& nodes(new_head, ?filtered_vs) &*& foreach(filtered_vs, (|x| p(x) && true));
{
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            assert node(?curr, ?v, ?next);
            leak node(curr, v, next);
            filter_nodes(&raw mut (**n).next, p);
            close node(curr, v, _);
        } else {
            let next_ = (**n).next;
            open node(?curr, _, _);
            dealloc(curr as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        close nodes(null, nil);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, _),
    ensures emp;
{
    if !n.is_null() {
        open nodes(n, ?vs);
        assert vs == cons(?h, ?t);
        open node(n, h, ?next);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        close nodes(null, nil);
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp,
        ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close struct_Stack_head(stack, null);
        close struct_Stack_padding(stack);
        close stack(stack, nil);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?vs),
        ensures stack(stack, cons(value, vs));
    {
        open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        close node(n, value, (*stack).head);
        (*stack).head = n;
        close struct_Stack_head(stack, n);
        close struct_Stack_padding(stack);
        close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, cons(?v, ?vs)),
        ensures stack(stack, vs) &*& result == v;
    {
        open stack(stack, cons(v, vs));
        let head = (*stack).head;
        open node(head, v, ?next);
        (*stack).head = next;
        close struct_Stack_head(stack, next);
        close struct_Stack_padding(stack);
        close stack(stack, vs);
        dealloc(head as *mut u8, Layout::new::<Node>());
        v
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack, ?vs) &*& foreach(vs, p),
        ensures stack(stack, ?filtered_vs) &*& foreach(filtered_vs, (|x| p(x) && true));
    {
        open stack(stack, vs);
        let head = (*stack).head;
        close nodes(head, vs);
        filter_nodes(&raw mut (*stack).head, p);
        open nodes(_, ?filtered_vs);
        close struct_Stack_head(stack, _);
        close struct_Stack_padding(stack);
        close stack(stack, filtered_vs);
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, _),
        ensures emp;
    {
        open stack(stack, _);
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
    requires true,
    ensures result == (x != 20);
{
    x != 20
}

fn main()
    requires emp,
    ensures emp;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}