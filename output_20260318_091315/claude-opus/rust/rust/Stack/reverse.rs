use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(struct Node *n; int v, struct Node *next) = n->value |-> v &*& n->next |-> next;

predicate nodes(struct Node *head) = 
    head == std::ptr::null_mut() ? emp : node(head, ?v, ?next) &*& nodes(next);

predicate stack(struct Stack *s; struct Node *head) = s->head |-> head &*& nodes(head);

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack, ?head))]
    #[ensures(stack(stack, cons(?v, head)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, cons(?v, ?next)))]
    #[ensures(stack(stack, next))]
    #[ensures(result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, ?head))]
    #[ensures(stack(stack, ?reversed))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(nodes(n) &*& nodes(m) &*& stack(stack, ?h) &*& h == append_rev(nodes_to_list(n), nodes_to_list(m)))]
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
    }

    #[requires(stack(stack, ?head))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fixpoint list<int> nodes_to_list(struct Node *head) {
    return head == std::ptr::null_mut() ? [] : cons((*head).value, nodes_to_list((*head).next));
}

fixpoint list<int> append_rev(list<int> xs, list<int> ys) {
    switch(xs) {
        case nil: return ys;
        case cons(x, xs0): return append_rev(xs0, cons(x, ys));
    }
}