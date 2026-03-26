use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; *mut Node next, i32 value) =
    n |-> struct Node { next: next, value: value };

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    s |-> struct Stack { head: ?head } &*&
    nodes == match nodes {
        cons(n, ns) => node(n, ?next, ?v) &*& stack_nodes(next, ns),
        nil => emp &*& head == std::ptr::null_mut(),
    };

predicate stack_nodes(*mut Node current; list<*mut Node> nodes) =
    match nodes {
        cons(n, ns) => current == n &*& node(n, ?next, ?v) &*& stack_nodes(next, ns),
        nil => current == std::ptr::null_mut(),
    };

lemma void stack_nodes_nil()
    requires stack_nodes(?current, nil);
    ensures current == std::ptr::null_mut();
{
}

lemma void stack_nodes_cons()
    requires stack_nodes(?current, cons(?n, ?ns));
    ensures current == n &*& node(n, ?next, ?v) &*& stack_nodes(next, ns);
{
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

    #[requires(stack(stack, ?s_nodes) &*& stack(other, ?o_nodes))]
    #[ensures(stack(stack, append(o_nodes, s_nodes)))]
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
    #[ensures(stack(stack, cons(?new_node, nodes)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, cons(?head_node, ?rest_nodes)))]
    #[ensures(stack(stack, rest_nodes) &*& result == ?val &*& node(head_node, _, val))]
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