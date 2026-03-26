use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>, v: T, next_node: *mut Node<T>) =
    n->Node { next: next_node, value: v };

predicate stack<T>(s: Stack<T>, contents: list<T>) =
    s.head |-> ?h &*& nodes(h, contents);

predicate nodes<T>(head: *mut Node<T>, contents: list<T>) =
    switch(contents) {
        Nil => head == 0,
        Cons(hd, tl) => 
            node(head, hd, ?next) &*& nodes(next, tl)
    };

#[requires(stack(s, ?contents))]
#[ensures(stack(s, cons(value, contents)))]
fn push<T>(s: &mut Stack<T>, value: T) {
    unsafe {
        let layout = Layout::new::<Node<T>>();
        let node_ptr = alloc(layout) as *mut Node<T>;
        if node_ptr.is_null() {
            handle_alloc_error(layout);
        }
        *node_ptr = Node { next: s.head, value: value };
        s.head = node_ptr;
    }
}

#[requires(stack(s, ?contents) &*& contents != Nil)]
#[ensures(stack(s, tail(contents)) &*& result == head(contents))]
fn pop<T>(s: &mut Stack<T>) -> T {
    unsafe {
        let node_ptr = s.head;
        let n = *node_ptr;
        s.head = n.next;
        let layout = Layout::new::<Node<T>>();
        let v = n.value;
        dealloc(node_ptr as *mut u8, layout);
        v
    }
}