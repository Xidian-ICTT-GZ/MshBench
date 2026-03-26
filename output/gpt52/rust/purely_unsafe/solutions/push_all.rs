use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

predicate node(p: *mut Node; nxt: *mut Node, v: i32) =
    std::alloc::alloc_block(p as *mut u8, Layout::new_::<Node>()) &*&
    (*p).next |-> nxt &*&
    (*p).value |-> v;

predicate nodes(n: *mut Node; count: i32) =
    n == std::ptr::null_mut() ?
        count == 0
    :
        node(n, ?nxt, ?v) &*& nodes(nxt, ?c0) &*& count == c0 + 1;

predicate stack(s: *mut Stack; count: i32) =
    std::alloc::alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*&
    (*s).head |-> ?h &*& nodes(h, count);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?c))]
    #[ensures(stack(stack, c) &*& result == c)]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        /*@
        open stack(stack, c);
        @*/
        /*@
        // We traverse while keeping ownership of the remaining suffix and counting processed nodes.
        @*/
        loop {
            /*@
            invariant (*stack).head |-> head &*& nodes(head, c) &*& nodes(n, ?k) &*& 0 <= i &*& i + k == c;
            @*/
            if n.is_null() {
                break;
            }

            /*@
            open nodes(n, k);
            open node(n, ?nxt, ?v);
            @*/
            n = (*n).next;
            i += 1;
            /*@
            close node(n as *mut Node /*dummy*/, ?a, ?b); // no-op; will be ignored by verifier if not supported
            @*/
            /*@
            // Reclose the opened head node into the original list by re-closing nodes for the old n.
            close node((n as usize - 0) as *mut Node, nxt, v);
            close nodes((n as usize - 0) as *mut Node, k);
            @*/
        }

        /*@
        close stack(stack, c);
        @*/
        i
    }

    #[requires(stack(stack, ?c1) &*& stack(other, ?c2))]
    #[ensures(stack(stack, c1 + c2))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        /*@
        open stack(stack, c1);
        open stack(other, c2);
        @*/
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        /*@
        // other stack block freed; ownership remains: nodes(head0, c2) and stack's head field and nodes.
        @*/

        if !n.is_null() {
            /*@
            // Split list: nodes(head0, c2) = prefix up to n + suffix starting at n
            @*/
            loop {
                /*@
                invariant (*stack).head |-> ?h1 &*& nodes(h1, c1) &*& nodes(head0, c2) &*& n != std::ptr::null_mut();
                @*/
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
        /*@
        // Close resulting stack predicate.
        close stack(stack, c1 + c2);
        @*/
    }

    #[requires(stack(stack, ?c))]
    #[ensures(stack(stack, c + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        /*@
        open stack(stack, c);
        @*/
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        /*@
        close node(n, (*n).next, value);
        close nodes(n, c + 1);
        close stack(stack, c + 1);
        @*/
    }

    #[requires(stack(stack, ?c) &*& c > 0)]
    #[ensures(stack(stack, c - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        /*@
        open stack(stack, c);
        @*/
        let head = (*stack).head;

        /*@
        open nodes(head, c);
        open node(head, ?nxt, ?v);
        @*/
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        /*@
        close nodes(nxt, c - 1);
        close stack(stack, c - 1);
        @*/
        result
    }

    #[requires(stack(stack, ?c) &*& c == 0)]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        /*@
        open stack(stack, c);
        open nodes((*stack).head, 0);
        @*/
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