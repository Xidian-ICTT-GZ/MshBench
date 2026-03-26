use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ pred nodes(?n, ?vals) = 
//@     switch n {
//@         | std::ptr::null_mut() => emp
//@         | _ => n |-> Node { next: ?next, value: ?v } &*& nodes(next, vals) &*& vals == cons(v, ?rest)
//@     };

//@ pred stack_pred(Stack *stack, list<int> vals) = 
//@     stack |-> Stack { head: ?head } &*& nodes(head, vals);

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack_pred(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack_pred(stack, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack_pred(stack, ?vals);
    //@ ensures stack_pred(stack, cons(value, vals));
    {
        //@ open stack_pred(stack, vals);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, cons(value, vals));
        //@ close stack_pred(stack, cons(value, vals));
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack_pred(stack, ?vals) &*& vals != nil;
    //@ ensures stack_pred(stack, tail(vals)) &*& result == head(vals);
    {
        //@ open stack_pred(stack, vals);
        let head = (*stack).head;
        //@ open nodes(head, vals);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack_pred(stack, tail(vals));
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ requires stack_pred(stack, ?vals);
    //@ ensures stack_pred(stack, reverse(vals));
    {
        //@ open stack_pred(stack, vals);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ let mut rev = nil;
        loop {
            //@ if (n == std::ptr::null_mut()) {
            //@     close stack_pred(stack, reverse(vals));
            //@     break;
            //@ } else {
            //@     open nodes(n, ?ns);
            //@     close nodes(n, nil);
            //@ }
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ // Update rev accordingly if tracking
        }
        (*stack).head = m;
        //@ // At this point, head points to reversed list
        //@ // close stack_pred(stack, reverse(vals));
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack_pred(stack, nil);
    //@ ensures true;
    {
        //@ open stack_pred(stack, nil);
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