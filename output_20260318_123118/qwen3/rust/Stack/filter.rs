use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; i32 value, *mut Node next) =
    n != null &*&
    struct_Node_padding(n) &*&
    (*n).value |-> value &*&
    (*n).next |-> next;

predicate nodes(*mut Node head; list<i32> values) =
    match values {
        nil => head == null,
        cons(h, t) => node(head, h, ?next) * nodes(next, t)
    };

predicate stack(*mut Stack s; list<i32> values) =
    s != null &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    nodes(head, values);

predicate predicate_fn(I32Predicate p) = true;

#[requires(predicate_fn(p))]
#[ensures(match result {
    null => nodes(null, nil),
    _ => nodes(result, ?filtered) &*& filtered == filter_values(values, p)
})]
#[requires(nodes(n, values))]
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            (*n).next = next;
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

#[requires(nodes(n, _))]
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

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
    
    #[requires(stack(stack, ?old_values))]
    #[ensures(stack(stack, cons(value, old_values)))]
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

    #[requires(stack(stack, cons(?head_value, ?tail_values)))]
    #[ensures(stack(stack, tail_values) &*& result == head_value)]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(stack(stack, ?values) &*& predicate_fn(p))]
    #[ensures(stack(stack, ?filtered) &*& filtered == filter_values(values, p))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
    }
    
    #[requires(stack(stack, _))]
    unsafe fn dispose(stack: *mut Stack)
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

#[requires(true)]
#[ensures(result == (x != 20))]
unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}

pure fn filter_values(list<i32> values, I32Predicate p) -> list<i32>;
axiom filter_values_nil {p: I32Predicate}: filter_values(nil, p) == nil;
axiom filter_values_cons {h: i32, t: list<i32>, p: I32Predicate}:
    filter_values(cons(h, t), p) ==
        if p(h) then cons(h, filter_values(t, p)) else filter_values(t, p);