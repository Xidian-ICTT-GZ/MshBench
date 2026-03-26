use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(*mut Node n; i32 v, *mut Node next) =
    (*n).value |-> v &*& (*n).next |-> next;

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    (*s).head |-> ?head &*&
    stack_nodes(head, nodes);

predicate stack_nodes(*mut Node head; list<*mut Node> nodes) =
    match nodes {
        nil => head == std::ptr::null_mut(),
        cons(n, rest) => node(n, ?v, ?next) &*& stack_nodes(next, rest)
    };

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

    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, nodes) &*& result == length(nodes))]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        loop {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        i
    }

    #[requires(stack(stack, ?nodes1) &*& stack(other, ?nodes2))]
    #[ensures(stack(stack, append(nodes2, nodes1)))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, cons(?n, nodes)) &*& node(n, value, ?old_head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, cons(?n, ?rest)) &*& node(n, ?v, ?next))]
    #[ensures(stack(stack, rest) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, _))]
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

lemma void stack_nodes_append(list<*mut Node> xs, list<*mut Node> ys);
    requires stack_nodes(?head, xs) &*& stack_nodes(?tail, ys) &*& match xs { nil => head == tail, cons(_, rest) => stack_nodes(tail, rest) };
    ensures stack_nodes(head, append(xs, ys));
{
    open stack_nodes(head, xs);
    match xs {
        nil => {
            close stack_nodes(head, append(xs, ys));
        },
        cons(x, rest) => {
            stack_nodes_append(rest, ys);
            close stack_nodes(head, append(xs, ys));
        }
    }
}

lemma void length_append(list<t> xs, list<t> ys);
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    match xs {
        nil => (),
        cons(_, rest) => length_append(rest, ys)
    }
}