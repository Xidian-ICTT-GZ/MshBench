use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

// Predicate describing ownership of a singly linked list starting at n,
// with elements in the sequence vs.
// It owns the heap nodes and the values.
predicate nodes<T>(Node<T>* n, list<T> vs) =
    n == std::ptr::null_mut() ?
        emp
    :
        n->next |-> ?next_node &*& n->value |-> ?v &*& malloc_block<Node<T>>(n) &*& nodes(next_node, ?vs_rest) &*& vs == cons(v, vs_rest);

// Predicate describing ownership of a stack struct s pointing to a linked list vs.
predicate stack<T>(Stack<T>* s, list<T> vs) =
    s->head |-> ?head_node &*& nodes(head_node, vs);

// Function to create a new empty stack.
// Returns full ownership of stack(s) with empty list.
#[requires(true)]
#[ensures(stack(result, nil))]
fn stack_new<T>() -> Stack<T>* {
    let s = unsafe {
        let layout = Layout::new::<Stack<T>>();
        let p = alloc(layout) as Stack<T>*;
        if p.is_null() { handle_alloc_error(layout) }
        p
    };
    unsafe {
        (*s).head = std::ptr::null_mut();
    }
    s
}

// Function to push a value v onto stack s.
// Requires full ownership of stack(s, vs).
// Ensures ownership of stack(s, cons(v, vs)).
#[requires(stack(s, vs))]
#[ensures(stack(s, cons(v, vs)))]
fn stack_push<T>(s: Stack<T>*, v: T) {
    unsafe {
        let layout_node = Layout::new::<Node<T>>();
        let n = alloc(layout_node) as Node<T>*;
        if n.is_null() { handle_alloc_error(layout_node) }
        // Allocate Node and initialize fields
        (*n).value = v;
        (*n).next = (*s).head;
        (*s).head = n;
    }
}

// Function to pop a value from the stack.
// Requires stack(s, cons(v, vs)) non-empty.
// Ensures stack(s, vs) and returns v.
#[requires(stack(s, cons(v, vs)))]
#[ensures(stack(s, vs))]
#[ensures(result == v)]
fn stack_pop<T>(s: Stack<T>*) -> T {
    unsafe {
        let n = (*s).head;
        let v = (*n).value;
        (*s).head = (*n).next;
        let layout_node = Layout::new::<Node<T>>();
        dealloc(n as *mut u8, layout_node);
        v
    }
}

// Function to deallocate entire stack and all nodes, given ownership stack(s, vs).
#[requires(stack(s, vs))]
#[ensures(true)]
fn stack_free<T>(s: Stack<T>*, vs: list<T>) {
    open stack(s, vs);
    open nodes((*s).head, vs);
    let mut current = (*s).head;
    let layout_node = Layout::new::<Node<T>>();
    while current != std::ptr::null_mut()
        invariant nodes(current, ?rest_vs)
    {
        open nodes(current, rest_vs);
        let next = (*current).next;
        dealloc(current as *mut u8, layout_node);
        close nodes(next, ?vs_rest);
        current = next;
    }
    let layout_stack = Layout::new::<Stack<T>>();
    dealloc(s as *mut u8, layout_stack);
}