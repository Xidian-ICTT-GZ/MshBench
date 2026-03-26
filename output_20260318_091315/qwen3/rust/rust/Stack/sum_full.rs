use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; i32 value, *mut Node next) =
    n |-> struct Node { next: next, value: value };

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    match nodes {
        cons(h, t) => s |-> struct Stack { head: h } &*& node(h, ?v, ?next) &*& stack_nodes(next, t),
        nil => s |-> struct Stack { head: null }
    };

predicate stack_nodes(*mut Node current; list<*mut Node> nodes) =
    match nodes {
        cons(h, t) => current == h &*& node(h, ?v, ?next) &*& stack_nodes(next, t),
        nil => current == null
    };

lemma void stack_nodes_nil()
    requires stack_nodes(null, ?nodes);
    ensures nodes == nil;
{
    open stack_nodes(null, nodes);
}

lemma void stack_nodes_cons()
    requires stack_nodes(?n, ?nodes) &*& n != null;
    ensures nodes == cons(n, ?tail) &*& node(n, ?v, ?next) &*& stack_nodes(next, tail);
{
    open stack_nodes(n, nodes);
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires stack_nodes(node, ?nodes);
    ensures stack_nodes(node, nodes) &*& result == sum_values(nodes);
{
    let mut result = 0;
    if !node.is_null() {
        open stack_nodes(node, nodes);
        assert nodes == cons(node, ?tail);
        let tail_sum = get_nodes_sum((*node).next);
        close stack_nodes(node, nodes);
        result = (*node).value + tail_sum;
    } else {
        stack_nodes_nil();
    }
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        requires true;
        ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack, nil);
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack(stack, ?nodes);
        ensures stack(stack, nodes) &*& result == sum_values(nodes);
    {
        open stack(stack, nodes);
        let result = get_nodes_sum((*stack).head);
        close stack(stack, nodes);
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?nodes);
        ensures stack(stack, cons(?new_node, nodes));
    {
        open stack(stack, nodes);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, (*stack).head);
        close stack(stack, cons(n, nodes));
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, cons(?head_node, ?tail_nodes));
        ensures stack(stack, tail_nodes) &*& result == ?value &*& node(head_node, value, ?next);
    {
        open stack(stack, cons(head_node, tail_nodes));
        let head = (*stack).head;
        assert head == head_node;
        open node(head, ?value, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack(stack, tail_nodes);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, _);
        ensures true;
    {
        open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

pure fn sum_values(nodes: list<*mut Node>) -> i32 {
    match nodes {
        cons(n, tail) => ?v + sum_values(tail),
        nil => 0
    }
} when (node(n, v, _));

fn main()
    requires true;
    ensures true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}