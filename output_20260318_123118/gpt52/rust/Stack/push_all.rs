use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

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

predicate nodes(struct Node *n;) =
    n == 0 ?
        emp
    :
        node(n, ?next, ?value) &*& nodes(next);

predicate stack(struct Stack *s;) =
    s->head |-> ?h &*& nodes(h);

@*/

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(0);
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack);
        stack
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack) &*& result >= 0)]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        //@ open stack(stack);
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        //@ close nodes(n);
        loop {
            //@ invariant stack->head |-> head &*& nodes(n) &*& i >= 0;
            //@ open nodes(n);
            if n.is_null() {
                //@ close nodes(0);
                break;
            }

            n = (*n).next;
            i += 1;

            //@ close nodes(n);
        }

        //@ close stack(stack);
        i
    }

    #[requires(stack(stack) &*& stack(other))]
    #[ensures(stack(stack))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        //@ open stack(other);
        let head0 = (*other).head;
        //@ open nodes(head0);
        //@ close nodes(head0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open stack(stack);
            //@ close nodes(n);
            loop {
                //@ invariant stack->head |-> ?h &*& nodes(h) &*& nodes(n) &*& n != 0;
                //@ open nodes(n);
                if (*n).next.is_null() {
                    //@ close nodes(n);
                    break;
                }
                let next = (*n).next;
                //@ close nodes(n);
                n = next;
                //@ close nodes(n);
            }

            //@ open nodes(n);
            (*n).next = (*stack).head;
            //@ close node(n, (*stack).head, (*n).value);
            //@ open nodes((*stack).head);
            //@ close nodes((*stack).head);
            //@ close nodes(head0);
            (*stack).head = head0;
            //@ close stack(stack);
        } else {
            //@ open stack(stack);
            //@ close stack(stack);
        }
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ open nodes((*stack).head);
        //@ close nodes((*stack).head);
        //@ close nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }

    #[requires(stack(stack) &*& (*stack).head != 0)]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?v);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes(next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    #[requires(stack(stack) &*& (*stack).head == 0)]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack);
        //@ open nodes(0);
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