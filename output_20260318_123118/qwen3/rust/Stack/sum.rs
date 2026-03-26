use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; *mut Node next, i32 value) =
    n != null &*&
    struct_Node_padding(n) &*&
    struct_Node_next(n, next) &*&
    struct_Node_value(n, value);

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    s != null &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, ?head) &*&
    stack_nodes(head, nodes);

predicate stack_nodes(*mut Node head; list<*mut Node> nodes) =
    match nodes {
        nil => head == null,
        cons(n, rest) => node(n, ?next, _) &*& stack_nodes(next, rest) &*& head == n
    };

lemma void stack_nodes_unique()
    req stack_nodes(?head1, ?nodes1) &*& stack_nodes(?head2, ?nodes2);
    ens stack_nodes(head1, nodes1) &*& stack_nodes(head2, nodes2) &*&
        (head1 == head2 ? nodes1 == nodes2 : true);
{
    open stack_nodes(head1, nodes1);
    open stack_nodes(head2, nodes2);
    if head1 == null {
        assert head2 == null;
        close stack_nodes(head1, nodes1);
        close stack_nodes(head2, nodes2);
    } else {
        assert head1 != null;
        assert head2 != null;
        let next1 = _;
        let next2 = _;
        stack_nodes_unique();
        close stack_nodes(head1, nodes1);
        close stack_nodes(head2, nodes2);
    }
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    requires stack_nodes(nodes, ?ns) &*& sum_values(ns, ?sum);
    ensures stack_nodes(nodes, ns) &*& result == sum;
{
    let mut result = 0;
    
    if !nodes.is_null() {
        open stack_nodes(nodes, ns);
        assert ns == cons(?n, ?rest);
        let v = _;
        assert node(n, ?next, v);
        let r = get_nodes_sum(next);
        result = r + v;
        close stack_nodes(nodes, ns);
    }
    
    result
}

predicate sum_values(list<*mut Node> nodes; i32 sum) =
    match nodes {
        nil => sum == 0,
        cons(n, rest) => node(n, _, ?v) &*& sum_values(rest, ?s) &*& sum == v + s
    };

lemma void sum_values_lemma()
    req sum_values(?ns, ?s);
    ens sum_values(ns, s);
{
    open sum_values(ns, s);
    match ns {
        nil => {
            close sum_values(ns, s);
        },
        cons(n, rest) => {
            let v = _;
            sum_values_lemma();
            close sum_values(ns, s);
        }
    }
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
        close stack(result, nil);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        requires stack(stack, ?nodes);
        ensures stack(stack, nodes) &*& result == (nodes == nil);
    {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires stack(stack, ?nodes) &*& sum_values(nodes, ?sum);
        ensures stack(stack, nodes) &*& sum_values(nodes, sum) &*& result == sum;
    {
        let result = get_nodes_sum((*stack).head);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?nodes);
        ensures stack(stack, cons(?n, nodes)) &*& node(n, ?old_head, value);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, (*n).next, value);
        close stack(stack, cons(n, nodes));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, cons(?n, ?rest)) &*& node(n, ?next, ?v);
        ensures stack(stack, rest) &*& result == v;
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        open node(n, next, v);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?nodes);
        ensures true;
    {
        let mut n = (*stack).head;
        loop 
            invariant stack_nodes(n, ?current_nodes) &*& stack_nodes((*stack).head, ?all_nodes) &*&
                      append(current_nodes, ?prefix, all_nodes) == true;
        {
            if n.is_null() {
                break;
            }
            open stack_nodes(n, current_nodes);
            assert current_nodes == cons(?node_ptr, ?rest_nodes);
            let next = (*n).next;
            open node(node_ptr, _, _);
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
            current_nodes = rest_nodes;
        }
        open stack(stack, nodes);
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