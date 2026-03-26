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
        cons(n, ns) => node(n, ?next, _) &*& stack_nodes(next, ns) &*& head == n
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
        if head2 == null {
            assert false;
        }
        assert head2 != null;
        let next1 = _;
        let next2 = _;
        stack_nodes_unique();
        close stack_nodes(head1, nodes1);
        close stack_nodes(head2, nodes2);
    }
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    req stack_nodes(nodes, ?ns) &*& foreach(ns, (|n| node(n, _, ?v) &*& v |-> ?value)) &*&
        foreach(ns, (|n| node(n, _, ?v) &*& v |-> ?value)) == foreach(ns, (|n| node(n, _, ?v) &*& v |-> ?value));
    ens stack_nodes(nodes, ns) &*& foreach(ns, (|n| node(n, _, ?v) &*& v |-> ?value)) &*&
        result == sum(foreach_map(ns, (|n| { let v = _; node(n, _, v); v })));

{
    let mut result = 0;
    
    if !nodes.is_null() {
        open stack_nodes(nodes, ns);
        assert ns == cons(nodes, ?rest);
        let next = (*nodes).next;
        let value = (*nodes).value;
        result = get_nodes_sum(next);
        result += value;
        close stack_nodes(nodes, ns);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        req true;
        ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close struct_Stack_head(stack, null);
        close struct_Stack_padding(stack);
        close stack(stack, nil);
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        req stack(stack, ?nodes);
        ens stack(stack, nodes) &*& result == (nodes == nil);
    {
        
        let head = (*stack).head;
        open stack(stack, nodes);
        let result = head == null;
        close stack(stack, nodes);
        
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        req stack(stack, ?nodes) &*& foreach(nodes, (|n| node(n, _, ?v) &*& v |-> ?value));
        ens stack(stack, nodes) &*& foreach(nodes, (|n| node(n, _, ?v) &*& v |-> ?value)) &*&
            result == sum(foreach_map(nodes, (|n| { let v = _; node(n, _, v); v })));
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        req stack(stack, ?nodes) &*& foreach(nodes, (|n| node(n, _, ?v) &*& v |-> ?val));
        ens stack(stack, cons(?n, nodes)) &*& foreach(cons(n, nodes), (|m| node(m, _, ?v) &*& v |-> ?val));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        open stack(stack, nodes);
        close struct_Node_next(n, (*stack).head);
        close struct_Node_value(n, value);
        close struct_Node_padding(n);
        close node(n, (*stack).head, value);
        close stack_nodes(n, cons(n, nodes));
        close stack(stack, cons(n, nodes));
        close foreach(cons(n, nodes), (|m| node(m, _, ?v) &*& v |-> ?val));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        req stack(stack, cons(?n, ?nodes)) &*& foreach(cons(n, nodes), (|m| node(m, _, ?v) &*& v |-> ?val));
        ens stack(stack, nodes) &*& foreach(nodes, (|m| node(m, _, ?v) &*& v |-> ?val)) &*& result == ?value;
    {
        
        let head = (*stack).head;
        open stack(stack, cons(n, nodes));
        assert head == n;
        open foreach(cons(n, nodes), _);
        open node(n, ?next, value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack(stack, nodes);
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
        req stack(stack, ?nodes) &*& foreach(nodes, (|m| node(m, _, ?v) &*& v |-> ?val)) &*& n >= 0 &*& length(nodes) >= n;
        ens stack(stack, drop(n, nodes)) &*& foreach(drop(n, nodes), (|m| node(m, _, ?v) &*& v |-> ?val));
    {
        let mut i = 0;
        loop 
            invariant stack(stack, drop(i, nodes)) &*& foreach(drop(i, nodes), (|m| node(m, _, ?v) &*& v |-> ?val)) &*&
                      0 <= i &*& i <= n;
        {
            
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
        req stack(stack, ?nodes) &*& foreach(nodes, (|n| node(n, _, ?v) &*& v |-> ?value));
        ens true;
    {
        
        let mut n = (*stack).head;
        loop 
            invariant stack_nodes(n, ?remaining) &*& foreach(remaining, (|m| node(m, _, ?v) &*& v |-> ?val));
        {
            
            if n.is_null() {
                break;
            }
            
            let next = (*n).next;
            open foreach(remaining, _);
            open node(n, _, _);
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        
        open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
    req true;
    ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}