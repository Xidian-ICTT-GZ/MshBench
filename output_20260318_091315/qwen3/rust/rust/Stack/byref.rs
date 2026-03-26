use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node node; list<i32> values) =
    if node == std::ptr::null_mut() {
        values == []
    } else {
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        Nodes(next, ?tail) &*&
        values == cons(v, tail)
    };

predicate Stack_own(*mut Stack s; list<i32> values) =
    (*s).head |-> ?head &*&
    Nodes(head, values);

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires
        *n |-> ?node &*&
        Nodes(node, ?values) &*&
        foreach(values, (|v| p(v) || true)),
    ensures
        *n |-> ?node2 &*&
        Nodes(node2, filter_values(values, p)),
{
    if !(*n).is_null() {
        
        let keep = p((**n).value);
        if keep {
            
            filter_nodes(&raw mut (**n).next, p);
            
            
            
            
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires Nodes(n, _),
    ensures emp,
{
    
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        requires emp,
        ensures Stack_own(result, []),
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        requires Stack_own(stack, ?values),
        ensures Stack_own(stack, cons(value, values)),
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires Stack_own(stack, cons(?v, ?vs)),
        ensures Stack_own(stack, vs) &*& result == v,
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires Stack_own(stack, ?values),
        ensures Stack_own(stack, filter_values(values, p)),
    {
        
        
        filter_nodes(&raw mut (*stack).head, p);
        
        
        
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
        requires Stack_own(stack, _),
        ensures emp,
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
    requires true,
    ensures result == (x != 20),
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}

lemma void filter_values_lemma(list<i32> xs, I32Predicate p);
    requires foreach(xs, (|v| p(v) || true));
    ensures true;
{
    
    
}

pure fn filter_values(list<i32> xs, I32Predicate p): list<i32>;
    requires foreach(xs, (|v| p(v) || true));
    ensures true;
{
    match xs {
        nil => nil,
        cons(h, t) => if p(h) { cons(h, filter_values(t, p)) } else { filter_values(t, p) }
    }
}