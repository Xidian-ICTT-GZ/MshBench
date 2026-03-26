use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(Node<T>* n, list<T> vals) =
    n != std::ptr::null_mut()
    &*&
    n->value |-> ?v
    &*& n->next |-> ?next
    &*& malloc_block<Node<T>>(n)
    &*& node(next, ?tail) &*& vals == cons(v, tail)
    ||
    n == std::ptr::null_mut() &*& vals == nil;

predicate stack<T>(Stack<T>* s, list<T> vals) =
    s->head |-> ?h &*& node(h, vals);

#[requires(stack(s, ?vals))]
#[ensures(stack(s, cons(v, vals)))]
unsafe fn push<T>(s: *mut Stack<T>, v: T)
{
    let layout = Layout::new::<Node<T>>();
    let n = alloc(layout) as *mut Node<T>;
    if n.is_null() {
        handle_alloc_error(layout);
    }
    // at this point, we own malloc_block<Node<T>>(n)
    // build node(n, [v] + vals)
    (*n).value = v;
    (*n).next = (*s).head;

    (*s).head = n;
}

#[requires(stack(s, cons(?v, ?tail)))]
#[ensures(stack(s, tail) &*& result == v)]
unsafe fn pop<T>(s: *mut Stack<T>) -> T {
    let n = (*s).head;
    assert(n != std::ptr::null_mut());
    let value = (*n).value;
    let next = (*n).next;
    (*s).head = next;
    // deallocate n
    let layout = Layout::new::<Node<T>>();
    dealloc(n as *mut u8, layout);
    value
}

#[requires(stack(s, ?vals))]
#[ensures(stack(s, vals))]
unsafe fn drop_stack<T>(s: *mut Stack<T>) {
    while (*s).head != std::ptr::null_mut()
        invariant stack(s, ?vals0)
        // vals0 changes due to pop
    {
        let _ = pop(s);
    }
}

// initialization predicate for empty stack
predicate stack_empty<T>(Stack<T>* s) =
    s->head |-> std::ptr::null_mut();

#[requires(true)]
#[ensures(stack_empty(s))]
unsafe fn init_stack<T>(s: *mut Stack<T>) {
    (*s).head = std::ptr::null_mut();
}