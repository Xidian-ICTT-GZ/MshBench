use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node node; i32 value, *mut Node next) =
    node |-> struct Node { next: next, value: value };

predicate stack(*mut Stack stack; list<*mut Node> nodes) =
    stack |-> struct Stack { head: ?head } &*& nodes == nodes_from(head);

predicate nodes_from(*mut Node head; list<*mut Node> nodes) =
    match nodes {
        nil => head == null,
        cons(node, rest) => node != null &*& node(node; ?value, ?next) &*& nodes_from(next, rest)
    };

lemma void nodes_from_unique(*mut Node head, list<*mut Node> nodes1, list<*mut Node> nodes2)
    requires nodes_from(head, nodes1) &*& nodes_from(head, nodes2);
    ensures nodes_from(head, nodes1) &*& nodes_from(head, nodes2) &*& nodes1 == nodes2;
{
    open nodes_from(head, nodes1);
    open nodes_from(head, nodes2);
    match nodes1 {
        nil => match nodes2 {
            nil => (),
            cons(n, _) => ()
        },
        cons(n1, rest1) => match nodes2 {
            nil => (),
            cons(n2, rest2) => {
                assert n1 == n2;
                nodes_from_unique((*n1).next, rest1, rest2);
            }
        }
    }
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires nodes_from(node, ?nodes);
    ensures nodes_from(node, nodes) &*& result == sum_values(nodes);
{
    let mut result = 0;
    if !node.is_null() {
        open nodes_from(node, _);
        let tail_sum = get_nodes_sum((*node).next);
        close nodes_from(node, _);
        result = (*node).value + tail_sum;
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
        requires stack(stack, cons(?head_node, ?rest));
        ensures stack(stack, rest) &*& result == node_value(head_node);
    {
        open stack(stack, cons(head_node, rest));
        open node(head_node, _, ?next);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack(stack, rest);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, nil);
        ensures true;
    {
        open stack(stack, nil);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fixpoint i32 node_value(*mut Node node) {
    match node {
        null => 0,
        _ => ?value 
    }
}

fixpoint i32 sum_values(list<*mut Node> nodes) {
    match nodes {
        nil => 0,
        cons(node, rest) => ?val + sum_values(rest) 
    }
}

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