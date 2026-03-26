use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate nodes(*mut Node n; list<i32> vs) =
    n == 0 ?
        vs == nil
    :
        (*n).next |-> ?next &*& (*n).value |-> ?v &*&
        nodes(next; ?vs0) &*&
        vs == cons(v, vs0);

predicate stack(*mut Stack s; list<i32> vs) =
    (*s).head |-> ?h &*& nodes(h; vs);

@*/

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

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, reverse(vs)))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        /*@
        // Establish:
        // nodes(n; vsn) * nodes(m; vsm) and vs == append(reverse(vsm), vsn)
        @*/
        loop {
            /*@
            invariant
                nodes(n; ?vsn) &*& nodes(m; ?vsm) &*&
                vs == append(reverse(vsm), vsn);
            @*/
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

    #[requires(stack(stack, ?vs) &*& vs == nil)]
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
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}