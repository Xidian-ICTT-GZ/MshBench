use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node_list(struct Node* n; list<i32> vs) =
    n == 0 ?
        vs == nil
    :
        n->next |-> ?nx &*& n->value |-> ?v &*& node_list(nx; ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct Stack* s; list<i32> vs) =
    s->head |-> ?h &*& node_list(h; vs);

fixpoint int sum_list(list<i32> vs) {
    switch (vs) {
        case nil: return 0;
        case cons(h, t): return h + sum_list(t);
    }
}

@*/

#[requires(node_list(nodes, ?vs))]
#[ensures(node_list(nodes, vs) &*& result == sum_list(vs))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, vs) &*& result == (vs == nil))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        result
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, vs) &*& result == sum_list(vs))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
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

    #[requires(stack(stack, ?vs) &*& 0 <= n &*& n <= length(vs))]
    #[ensures(stack(stack, drop(n, vs)))]
    unsafe fn popn(stack: *mut Stack, n: i32) {
        let mut i = 0;
        loop {
            /*@
            invariant stack(stack, ?vs0) &*& 0 <= i &*& i <= n &*& vs0 == drop(i, vs) &*& n <= length(vs);
            @*/
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        let mut n = (*stack).head;
        loop {
            /*@
            invariant stack->head |-> ?h &*& node_list(n, ?vsn) &*& node_list(h, ?vsh) &*& vs == append(reverse(?prefix), vsh) &*& vsh == vsn;
            @*/
            if n.is_null() {
                break;
            }

            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }

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