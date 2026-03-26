use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred node(n: *mut Node; next: *mut Node, value: i32) = n != 0i32 as *mut Node &*& struct_Node_padding(n) &*& (*n).next |-> next &*& (*n).value |-> value;
//@ pred stack(s: *mut Stack; head: *mut Node) = s != 0i32 as *mut Stack &*& struct_Stack_padding(s) &*& (*s).head |-> head;

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, 0i32 as *mut Node);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, 0i32 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?head);
    //@ ens stack(stack, ?new_head);
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ open stack(stack, head);
        //@ close stack(stack, n);
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head) &*& head != 0i32 as *mut Node &*& node(head, ?next, ?value);
    //@ ens stack(stack, next) &*& result == value;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, head);
        //@ open node(head, ?next, ?value);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ req stack(stack, ?orig_head);
    //@ ens stack(stack, ?rev_head);
    {
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ open stack(stack, orig_head);
        //@ stack_reverse_ghost(n, m);
        
        
        loop {
            
            if n.is_null() {
                break;
            }
            //@ open stack_reverse_inv(n, m);
            
            let next = (*n).next;
            //@ open node(n, next, _);
            
            (*n).next = m;
            //@ close node(n, m, _);
            m = n;
            n = next;
            //@ close stack_reverse_inv(n, m);
            
            
        }
        //@ open stack_reverse_inv(0i32 as *mut Node, rev_head);
        (*stack).head = m;
        //@ close stack(stack, rev_head);
        
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        //@ open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ pred stack_reverse_inv(n: *mut Node, m: *mut Node) =
//@   stack_nodes(n, ?xs) &*& stack_nodes_rev(m, xs);

//@ fixpoint bool stack_nodes(*mut Node n, list<i32> vs) {
//@   match vs {
//@     nil => return n == 0i32 as *mut Node,
//@     cons(v, vs1) => return n != 0i32 as *mut Node && node(n, ?next, v) && stack_nodes(next, vs1)
//@   }
//@ }

//@ fixpoint bool stack_nodes_rev(*mut Node n, list<i32> vs) {
//@   match vs {
//@     nil => return n == 0i32 as *mut Node,
//@     cons(v, vs1) => return n != 0i32 as *mut Node && node(n, ?next, v) && stack_nodes_rev(next, vs1)
//@   }
//@ }

//@ lemma void stack_reverse_ghost(*mut Node n, *mut Node m)
//@ req stack_nodes(n, ?vs) &*& stack_nodes_rev(m, nil);
//@ ens stack_reverse_inv(n, m);
//@ {
//@   close stack_reverse_inv(n, m);
//@ }

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}