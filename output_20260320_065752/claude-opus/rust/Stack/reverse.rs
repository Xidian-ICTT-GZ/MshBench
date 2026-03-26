use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ 
predicate node(struct Node* n; int value, struct Node* next) = 
    n->value |-> value &*& n->next |-> next; 

predicate stack(struct Stack* s; list<int> vs) =
    s->head |-> ?head &*& nodes(head, vs);

fixpoint list<int> appendrev(list<int> xs, list<int> ys) =
    switch(xs) {
        case nil: ys
        case cons(x,xs0): appendrev(xs0, cons(x, ys))
    };
    
predicate nodes(struct Node* n, list<int> vs) =
    vs == nil ? n == null : n != null &*& node(n, head(vs), ?next) &*& nodes(next, tail(vs));

fixpoint int head(list<int> xs) {
    switch(xs) {
        case nil: 0
        case cons(x, _) => x
    }
}

fixpoint list<int> tail(list<int> xs) {
    switch(xs) {
        case nil: nil
        case cons(_, xs0) => xs0
    }
}
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    //@ req true;
    //@ ensures stack(result, nil);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close stack(stack, nil);
        stack
    }
    
    //@ req stack(stack, ?vs);
    //@ ensures stack(stack, cons(value, vs));
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, value, (*n).next);
        //@ close nodes(n, cons(value, vs));
        //@ close stack(stack, cons(value, vs));
    }
    
    //@ req stack(stack, ?vs) &*& vs != nil;
    //@ ensures stack(stack, tail(vs));
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, vs);
        let head = (*stack).head;
        //@ open nodes(head, ?vons);
        //@ open node(head, ?val, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close nodes(next, tail(vs));
        //@ close stack(stack, tail(vs));
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    //@ req stack(stack, ?vs);
    //@ ensures stack(stack, reverse(vs));
    unsafe fn reverse(stack: *mut Stack)
    {
        //@ open stack(stack, vs);
        let mut n = (*stack).head;
        //@ open nodes(n, vs);
        let mut m = std::ptr::null_mut();

        /*@ 
        predicate loop_invariant(struct Node* n, struct Node* m, list<int> nvs, list<int> mvs) =
            nodes(n, nvs) &*& nodes(m, mvs);
        @*/

        //@ pred reverse_acc(list<int> l1, list<int> l2) = appendrev(l1, l2) == vs;

        //@ let rec reverse_loop(n, m, nvs, mvs) = 
        //@     if(n == null) {
        //@         appendrev(nvs, mvs) == vs
        //@     } else {
        //@         head(nvs) == (*n).value &*& tail(nvs) == nodes((*n).next, ?nnvs) &*& reverse_loop((*n).next, n, nnvs, cons((*n).value, mvs))
        //@     };

        //@ reverse_loop(n, m, vs, nil);
        
        loop {
            //@ open nodes(n, ?nvs);
            if n.is_null() {
                break;
            }

            let next = (*n).next;
            
            (*n).next = m;
            m = n;
            n = next;

            //@ open nodes(next, ?nnvs);
            //@ close nodes(n, cons((*n).value, mvs));
            //@ close nodes(m, cons((*m).value, mvs));
        }
        (*stack).head = m;
        //@ close stack(stack, appendrev(nil, reverse(vs))); 
        //@ assert appendrev(nil, reverse(vs)) == reverse(vs);
        //@ close stack(stack, reverse(vs));
    }

    //@ req stack(stack, ?vs);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, vs);
        //@ open nodes((*stack).head, ?vs);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

/*@ 
fixpoint list<int> reverse(list<int> xs) {
    switch(xs) {
        case nil: nil
        case cons(x, xs0): appendrev(reverse(xs0), cons(x,nil))
    }
}
@*/

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