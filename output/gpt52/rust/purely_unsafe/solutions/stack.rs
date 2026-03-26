use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(struct Node *n; struct Node *next, i32 value) =
    n->next |-> next &*& n->value |-> value;

predicate nodes(struct Node *n; list<i32> vs) =
    n == 0 ?
        vs == nil
    :
        node(n, ?next, ?v) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct Stack *s; list<i32> vs) =
    s->head |-> ?h &*& nodes(h, vs);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(result as *mut Stack != std::ptr::null_mut() &*& stack(result as *mut Stack, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, cons(?v, ?vs0)))]
    #[ensures(stack(stack, vs0) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack, nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}