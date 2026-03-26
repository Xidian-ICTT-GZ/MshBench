use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node_list(*mut Node n;);

predicate stack_inv(*mut Stack s;) =
    s |-> ?head &*& node_list(head);

lemma void node_list_nil()
    requires true;
    ensures node_list(null);
{
    close node_list(null);
}

lemma void node_list_cons(*mut Node n)
    requires n |-> ?next &*& node_list(next);
    ensures node_list(n);
{
    close node_list(n);
}

lemma void node_list_unfold(*mut Node n)
    requires node_list(n);
    ensures n == null || (n |-> ?next &*& node_list(next));
{
    open node_list(n);
}

#[requires(node_list(nodes))]
#[ensures(node_list(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        node_list_unfold(nodes);
        assert(nodes |-> ?next &*& node_list(next));
        result = get_nodes_sum(next);
        result += (*nodes).value;
        node_list_cons(nodes);
    } else {
        node_list_nil();
    }

    result
}

impl Stack {
    #[requires(true)]
    #[ensures(stack_inv(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        node_list_nil();
        close stack_inv(stack);
        stack
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        open stack_inv(stack);
        let head = (*stack).head;
        close stack_inv(stack);
        head.is_null()
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        open stack_inv(stack);
        let head = (*stack).head;
        let result = get_nodes_sum(head);
        close stack_inv(stack);
        result
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack_inv(stack);
        let head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = head;
        (*n).value = value;
        (*stack).head = n;
        node_list_cons(n);
        close stack_inv(stack);
    }

    #[requires(stack_inv(stack))]
    #[ensures(stack_inv(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open stack_inv(stack);
        let head = (*stack).head;
        node_list_unfold(head);
        assert(head != null);
        assert(head |-> ?next &*& node_list(next));
        let result = (*head).value;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack_inv(stack);
        result
    }

    #[requires(stack_inv(stack) &*& n >= 0)]
    #[ensures(stack_inv(stack))]
    unsafe fn popn(stack: *mut Stack, n: i32) {
        let mut i = 0;
        loop invariant stack_inv(stack) &*& 0 <= i &*& i <= n;
        {
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }

    #[requires(stack_inv(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack_inv(stack);
        let mut n = (*stack).head;
        while !n.is_null()
            invariant node_list(n);
        {
            node_list_unfold(n);
            assert(n |-> ?next &*& node_list(next));
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