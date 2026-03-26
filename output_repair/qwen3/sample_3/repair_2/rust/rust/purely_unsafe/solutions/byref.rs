use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate node(n: *mut Node; next: *mut Node, value: i32) =
    n != std::ptr::null_mut() &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

predicate nodes(n: *mut Node; values: list<i32>) =
    match values {
        Nil => n == std::ptr::null_mut(),
        Cons(h, t) => exists(next: *mut Node). node(n, next, h) &*& nodes(next, t)
    };

predicate stack(s: *mut Stack; values: list<i32>) =
    s != std::ptr::null_mut() &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    nodes(head, values);

lemma void nodes_split(*mut Node n, list<i32> vs)
    requires nodes(n, vs);
    ensures nodes(n, vs);
{
    admit();
}

lemma void nodes_join(*mut Node n, list<i32> vs)
    requires nodes(n, vs);
    ensures nodes(n, vs);
{
    admit();
}

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires *n |-> ?head &*& nodes(head, ?vs) &*&
             forall(vs, lambda(x: i32). p(x) || !p(x));
    ensures *n |-> ?new_head &*& nodes(new_head, ?filtered_vs) &*&
            foreach(filtered_vs, lambda(x: i32). p(x)) &*&
            foreach(vs, lambda(x: i32). mem(x, filtered_vs) || !p(x));
{
    if !(*n).is_null() {
        let head = *n;
        open nodes(head, _);
        assert node(head, ?next, ?val);
        let keep = p(val);
        if keep {
            close node(head, next, val);
            filter_nodes(&raw mut (**n).next, p);
            open nodes(next, _);
        } else {
            let next_ = (**n).next;
            close node(head, next_, val);
            dealloc(head as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, ?vs);
    ensures emp;
{
    if !n.is_null() {
        open nodes(n, _);
        assert node(n, ?next, ?val);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(emp)]
    #[ensures(stack(result, Nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, Cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, Cons(?v, ?vs)))]
    #[ensures(stack(stack, vs) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, ?vs) &*& forall(vs, lambda(x: i32). p(x) || !p(x)))]
    #[ensures(stack(stack, ?filtered_vs) &*& foreach(filtered_vs, lambda(x: i32). p(x)) &*& foreach(vs, lambda(x: i32). mem(x, filtered_vs) || !p(x)))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        filter_nodes(&raw mut (*stack).head, p);
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(true)]
#[ensures(result == (x != 20))]
unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

#[requires(emp)]
#[ensures(emp)]
fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}