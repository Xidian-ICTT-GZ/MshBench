use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; *mut Node next, i32 value) = 
    n |-> struct Node { next: next, value: value };

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    s |-> struct Stack { head: ?head } &*&
    nodes == match nodes {
        cons(n, rest) => node(n, ?next, _) &*& stack_nodes(next, rest),
        nil => emp &*& head == std::ptr::null_mut(),
    };

predicate stack_nodes(*mut Node head; list<*mut Node> nodes) =
    match nodes {
        cons(n, rest) => node(n, ?next, _) &*& stack_nodes(next, rest) &*& head == n,
        nil => emp &*& head == std::ptr::null_mut(),
    };

lemma void stack_nodes_nil()
    requires stack_nodes(?head, nil);
    ensures head == std::ptr::null_mut();
{
    open stack_nodes(_, _);
}

lemma void stack_nodes_cons()
    requires stack_nodes(?head, cons(?n, ?rest));
    ensures node(n, ?next, _) &*& stack_nodes(next, rest) &*& head == n;
{
    open stack_nodes(_, _);
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires stack_nodes(nodes, ?ns) &*& foreach(ns, (|n| node(n, _, ?v) &*& v >= 0)) == true;
    ensures stack_nodes(nodes, ns) &*& foreach(ns, (|n| node(n, _, ?v) &*& v >= 0)) == true &*& result == sum_ints(map_ints(ns));
{
    let mut result = 0;
    
    if !nodes.is_null() {
        assert stack_nodes(nodes, cons(?n, ?rest));
        assert node(n, ?next, ?v);
        close stack_nodes(next, rest);
        result = get_nodes_sum(next);
        open stack_nodes(next, rest);
        result += v;
        close stack_nodes(nodes, cons(n, rest));
    } else {
        assert stack_nodes(nodes, nil);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        requires emp;
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
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack(stack, ?nodes);
        ensures stack(stack, nodes) &*& result == (nodes == nil);
    {
        
        let head = (*stack).head;
        open stack(stack, nodes);
        let result = head.is_null();
        close stack(stack, nodes);
        
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack(stack, ?nodes) &*& foreach(nodes, (|n| node(n, _, ?v) &*& v >= 0)) == true;
        ensures stack(stack, nodes) &*& foreach(nodes, (|n| node(n, _, ?v) &*& v >= 0)) == true &*& result == sum_ints(map_ints(nodes));
    {
        open stack(stack, nodes);
        let result = get_nodes_sum((*stack).head);
        close stack(stack, nodes);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?nodes) &*& value >= 0;
        ensures stack(stack, cons(?n, nodes));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        open stack(stack, nodes);
        close node(n, (*n).next, value);
        close stack(stack, cons(n, nodes));
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, cons(?n, ?rest));
        ensures stack(stack, rest) &*& result >= 0;
    {
        open stack(stack, cons(n, rest));
        assert node(n, ?next, ?v);
        let head = (*stack).head;
        
        let result = v;
        (*stack).head = next;
        close stack(stack, rest);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?nodes);
        ensures emp;
    {
        open stack(stack, nodes);
        let mut n = (*stack).head;
        loop 
            invariant stack_nodes(n, nodes) &*& stack(stack, nil) &*& (*stack).head == n;
        {
            
            if n.is_null() {
                break;
            }
            open stack_nodes(n, cons(?curr, ?rest));
            assert node(curr, ?next, _);
            let next = (*curr).next;
            dealloc(curr as *mut u8, Layout::new::<Node>());
            n = next;
            nodes = rest;
            close stack_nodes(n, rest);
        }
        open stack_nodes(n, nil);
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

fixpoint int sum_ints(list<int> xs) {
    match xs {
        nil => 0,
        cons(x, xs0) => x + sum_ints(xs0)
    }
}

fixpoint list<int> map_ints(list<*mut Node> ns) {
    match ns {
        nil => nil,
        cons(n, ns0) => cons(?v, map_ints(ns0)) 
    }
}