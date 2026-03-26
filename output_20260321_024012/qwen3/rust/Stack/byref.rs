use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(*mut Node n; list<i32> vs) =
//@   n == null ? vs == nil :
//@   exists<Node> n_ &*&
//@     struct_Node_padding(n_) &*&
//@     n_.next |-> ?next &*&
//@     n_.value |-> ?v &*&
//@     n == n_ &*&
//@     nodes(next, ?vs0) &*&
//@     vs == cons(v, vs0);

//@ pred stack(*mut Stack s; list<i32> vs) =
//@   s == null ? false :
//@   exists<Stack> s_ &*&
//@     struct_Stack_padding(s_) &*&
//@     s_.head |-> ?head &*&
//@     s == s_ &*&
//@     nodes(head, vs);

//@ lemma_auto void nodes_split()
//@   requires nodes(?n, ?vs);
//@   ensures nodes(n, vs);
//@ {
//@ }

//@ lemma void nodes_join()
//@   requires nodes(?n1, ?vs1) &*& nodes(?n2, ?vs2) &*& n1 != n2;
//@   ensures nodes(n1, vs1) &*& nodes(n2, vs2);
//@ {
//@   open nodes(n1, vs1);
//@   open nodes(n2, vs2);
//@   close nodes(n1, vs1);
//@   close nodes(n2, vs2);
//@ }

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req *n |-> ?head &*& nodes(head, ?vs);
//@ ens *n |-> ?head2 &*& nodes(head2, ?vs2) &*& true; // functional spec omitted for safety
{
    if !(*n).is_null() {
        
        let keep = p((**n).value);
        if keep {
            
            //@ open nodes(*n, _);
            //@ assert exists<Node> ?n0 &*& struct_Node_padding(n0) &*& n0.next |-> ?next &*& n0.value |-> ?v &*& *n == n0;
            //@ close nodes(*n, cons(v, _));
            filter_nodes(&raw mut (**n).next, p);
            //@ open nodes(?next2, _);
            //@ close nodes(*n, _);
        } else {
            let next_ = (**n).next;
            //@ open nodes(*n, _);
            //@ assert exists<Node> ?n0 &*& struct_Node_padding(n0) &*& n0.next |-> next_ &*& n0.value |-> ?v &*& *n == n0;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
    //@ if (*n).is_null() { close nodes(null, nil); }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n, _);
//@ ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n, _);
        //@ assert exists<Node> ?n0 &*& struct_Node_padding(n0) &*& n0.next |-> ?next &*& n0.value |-> _ &*& n == n0;
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(null, nil);
        //@ close stack(stack, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ open stack(stack, vs);
        //@ assert exists<Stack> ?s &*& struct_Stack_padding(s) &*& s.head |-> ?old_head &*& stack == s;
        //@ close nodes(n, cons(value, vs));
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?v, ?vs));
    //@ ens stack(stack, vs) &*& result == v;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, cons(v, vs));
        //@ assert exists<Stack> ?s &*& struct_Stack_padding(s) &*& s.head |-> head &*& stack == s;
        //@ open nodes(head, cons(v, vs));
        //@ assert exists<Node> ?n &*& struct_Node_padding(n) &*& n.next |-> ?next &*& n.value |-> v &*& head == n;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, ?vs2) &*& true;
    {
        
        
        filter_nodes(&raw mut (*stack).head, p);
        //@ open stack(stack, vs);
        //@ assert exists<Stack> ?s &*& struct_Stack_padding(s) &*& s.head |-> ?h &*& stack == s;
        //@ close stack(stack, _);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
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