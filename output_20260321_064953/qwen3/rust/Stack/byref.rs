use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(*mut Node n; list<i32> vs) =
//@   n == null ? vs == [] :
//@   exists<Node> n_ &*&
//@     struct_Node_padding(n_) &*&
//@     n_.next |-> ?next &*&
//@     n_.value |-> ?v &*&
//@     nodes(next, ?vs0) &*&
//@     vs == cons(v, vs0);

//@ pred stack(*mut Stack s; list<i32> vs) =
//@   s == null ? false :
//@   exists<Stack> s_ &*&
//@     struct_Stack_padding(s_) &*&
//@     s_.head |-> ?head &*&
//@     nodes(head, vs);

//@ lemma void nodes_non_null_unique(*mut Node n)
//@ requires nodes(n, ?vs) &*& n != null;
//@ ensures nodes(n, vs) &*& unique_ptr(n, Layout::new::<Node>()) &*& struct_Node_full(n);
//@ {
//@   open nodes(n, vs);
//@   assert exists<Node>(?n_);
//@   close_struct(n_);
//@   close unique_ptr(n, Layout::new::<Node>());
//@ }

//@ lemma void nodes_null()
//@ requires nodes(null, ?vs);
//@ ensures vs == [];
//@ {
//@   open nodes(null, vs);
//@ }

//@ lemma void stack_non_null_unique(*mut Stack s)
//@ requires stack(s, ?vs) &*& s != null;
//@ ensures stack(s, vs) &*& unique_ptr(s, Layout::new::<Stack>()) &*& struct_Stack_full(s);
//@ {
//@   open stack(s, vs);
//@   assert exists<Stack>(?s_);
//@   close_struct(s_);
//@   close unique_ptr(s, Layout::new::<Stack>());
//@ }

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)

{
    //@ open nodes(*n, ?vs);
    if !(*n).is_null() {
        //@ assert *n != null;
        //@ nodes_non_null_unique(*n);
        let keep = p((**n).value);
        if keep {
            //@ close nodes((*n), cons((**n).value, ?vs0));
            //@ open nodes((*n), _);
            filter_nodes(&raw mut (**n).next, p);
            //@ close nodes(*n, cons((**n).value, _));
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ open nodes(next_, ?vs1);
            filter_nodes(n, p);
            //@ close nodes(*n, vs1);
        }
    } else {
        //@ close nodes(null, []);
    }
    //@ close nodes(*n, _);
}

unsafe fn dispose_nodes(n: *mut Node)

{
    //@ open nodes(n, ?vs);
    if !n.is_null() {
        //@ nodes_non_null_unique(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
    //@ if (n == null) close nodes(null, []);
}

impl Stack {

    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close unique_ptr(stack, Layout::new::<Stack>());
        //@ close struct_Stack_full(stack);
        //@ close stack(stack, []);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        //@ open stack(stack, ?vs);
        //@ stack_non_null_unique(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close unique_ptr(n, Layout::new::<Node>());
        //@ close struct_Node_full(n);
        //@ close nodes(n, cons(value, vs));
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        //@ open stack(stack, ?vs);
        //@ stack_non_null_unique(stack);
        let head = (*stack).head;
        //@ open nodes(head, ?vs0);
        //@ assert vs == cons(?v, ?vs1);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs1);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    
    
    {
        //@ open stack(stack, ?vs);
        //@ stack_non_null_unique(stack);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack(stack, _);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack, ?vs);
        //@ stack_non_null_unique(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool

{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        //@ close stack(s, []);
        Stack::push(s, 10);
        //@ open stack(s, _);
        Stack::push(s, 20);
        //@ open stack(s, _);
        Stack::filter(s, neq_20);
        //@ open stack(s, _);
        Stack::dispose(s);
    }
}