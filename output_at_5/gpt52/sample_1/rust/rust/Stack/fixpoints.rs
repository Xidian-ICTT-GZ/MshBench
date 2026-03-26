use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list<*mut Node> ns;) =
    match ns {
        nil => true,
        cons(n, ns0) =>
            n != 0 &*&
            struct_Node_padding(n) &*&
            (*n).next |-> ?nx &*&
            (*n).value |-> ?v &*&
            nodes(ns0) &*&
            nx == (ns0 == nil ? 0 : head(ns0))
    };

pred stack(stack: *mut Stack; list<i32> vs) =
    stack != 0 &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?h &*&
    nodes(?ns) &*&
    h == (ns == nil ? 0 : head(ns)) &*&
    length(vs) == length(ns);

@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, nil);
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(nil);
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    
    
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ open nodes(?ns);
        //@ close nodes(cons(n, ns));
        (*stack).head = n;
        //@ close stack(stack, cons(value, vs));
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?v, ?vs0));
    //@ ens stack(stack, vs0) &*& result == v;
    
    
    {
        //@ open stack(stack, cons(v, vs0));
        let head = (*stack).head;
        
        //@ open nodes(?ns);
        //@ assert ns == cons(head, ?ns0);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open nodes(ns0);
        //@ close nodes(ns0);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, vs0);
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?vs);
    //@ ens true;
    
    
    {
        //@ open stack(stack, vs);
        //@ open nodes(?ns);
        //@ close nodes(ns); // no-op to keep predicate well-formed
        //@ leak nodes(ns);
        //@ leak struct_Stack_padding(stack);
        //@ leak (*stack).head |-> ?h;
        
        
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