use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@
predicate nodes(Node *n;) =
    n == 0 ? emp : n->value |-> _ &*& n->next |-> ?next &*& nodes(next);

predicate stack(Stack *s, list<int> vs;) =
    s->head |-> ?head &*& nodes(head);

fixpoint list<int> nodes_list(Node *n) {
    switch(n) {
        case 0: return nil;
        case cons(h, t): return cons(*(h->value), nodes_list(h->next));
    }
}

fixpoint list<int> reverse_list(list<int> xs) {
    switch(xs) {
        case nil: return nil;
        case cons(h, t): return append(reverse_list(t), cons(h, nil));
    }
}
@*/

struct Stack {
    head: *mut Node,
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires true;
    //@ ensures stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack, vs);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack(stack, cons(value, vs));
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vs) &*& vs != nil;
    //@ ensures stack(stack, tail(vs)) &*& result == head(vs);
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, tail(vs));
        result
    }
    
    unsafe fn reverse(stack: *mut Stack)
    //@ requires stack(stack, ?vs);
    //@ ensures stack(stack, reverse_list(vs));
    {
        //@ open stack(stack, vs);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        /*@
        predicate nodes_mut(Node *n, list<int> l1; ) = nodes(n) &*& nodes(m) &*& append(l1, reverse_list(nil)) == vs;
        @*/
        // loop invariant:
        // nodes(n) &*& nodes(m);
        while !n.is_null() {
            //@ open nodes(n);
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
            //@ close nodes(m);
        }
        (*stack).head = m;
        //@ close stack(stack, reverse_list(vs));
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, nil);
    //@ ensures true;
    {
        //@ open stack(stack, nil);
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