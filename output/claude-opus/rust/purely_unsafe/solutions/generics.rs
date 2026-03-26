use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*