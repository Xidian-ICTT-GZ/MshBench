use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>, value: T, next: *mut Node<T>) = 
    n->Node { next: next, value: value };

predicate stack_contents<T>(head: *mut Node<T>, list: list<T>) = 
    switch list {
        case nil => head == std::ptr::null_mut() &*& emp;
        case cons(h, t) => 
            node(head, h, ?next) &*& stack_contents(next, t);
    };

predicate stack<T>(s: &Stack<T>, contents: list<T>) = s->Stack { head: ?head } &*& stack_contents(head, contents);

#[requires(stack(s, ?contents))]
#[ensures(stack(s, cons(value, contents)))]
fn push<T>(s: &mut Stack<T>, value: T) {
    unsafe {
        let layout = Layout::new::<Node<T>>();
        let raw = alloc(layout) as *mut Node<T>;
        if raw.is_null() {
            handle_alloc_error(layout);
        }
        *raw = Node { next: s.head, value: value };
        s.head = raw;
    }
}

#[requires(stack(s, ?contents) &*& contents != nil)]
#[ensures(stack(s, tail(contents)) &*& result == head(contents))]
fn pop<T>(s: &mut Stack<T>) -> T {
    unsafe {
        let head_ptr = s.head;
        let Node { next, value } = *head_ptr;
        s.head = next;
        let layout = Layout::new::<Node<T>>();
        dealloc(head_ptr as *mut u8, layout);
        value
    }
}