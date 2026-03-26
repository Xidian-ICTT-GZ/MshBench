use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ pred node(p: *mut Node; next: *mut Node, value: i32) = 
    p != 0 &*& alloc_block(p as *u8, std::mem::size_of::<Node>()) &*& 
    struct_Node_padding(p) &*&
    (*p).next |-> next &*& (*p).value |-> value;
@*/

/*@ pred stack(p: *mut Stack; head: *mut Node) = 
    p != 0 &*& alloc_block(p as *u8, std::mem::size_of::<Stack>()) &*& 
    struct_Stack_padding(p) &*&
    (*p).head |-> head;
@*/

/*@ pred nodes(p: *mut Node; vs: list<i32>) =
    match vs {
        nil => p == 0,
        cons(v, rest) => exists(next: *mut Node). node(p, next, v) &*& nodes(next, rest)
    };
@*/

impl Stack {

    //@ req true;
    //@ ens stack(result, 0);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, 0);
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }
    
    //@ req stack(stack, ?old_head) &*& nodes(old_head, ?vs);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, cons(value, vs));
    unsafe fn push(stack: *mut Stack, value: i32)
    
    
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, (*stack).head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ open stack(stack, _);
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
    }
    
    //@ req stack(stack, ?old_head) &*& old_head != 0 &*& nodes(old_head, cons(?v, ?vs));
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, vs) &*& result == v;
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        
        let head = (*stack).head;
        //@ open stack(stack, _);
        //@ open nodes(head, _);
        //@ open node(head, _, _);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, (*stack).head);
        
        result
    }
    
    //@ req stack(stack, ?head) &*& nodes(head, ?vs);
    //@ ens stack(stack, ?rev_head) &*& nodes(rev_head, reverse(vs));
    unsafe fn reverse(stack: *mut Stack)
    
    
    {
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(m, nil);
        
        
        loop {
            //@ inv stack(stack, _) &*& nodes(n, ?vs1) &*& nodes(m, ?vs2) &*& append(vs2, vs1) == vs;
            //@ open stack(stack, _);
            
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n, _);
            //@ open node(n, ?next, ?v);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close node(n, m, v);
            //@ close nodes(n, cons(v, vs2));
            m = n;
            n = next;
            
            
        }
        //@ open stack(stack, _);
        (*stack).head = m;
        //@ close stack(stack, m);
        
    }

    //@ req stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    
    
    {
        //@ open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()

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