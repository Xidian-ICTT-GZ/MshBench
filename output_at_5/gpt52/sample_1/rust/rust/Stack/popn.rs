use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(list<i32> vs, *mut Node n) =
    n == 0 ?
        vs == nil
    :
        (*n).next |-> ?nx &*& (*n).value |-> ?v &*& nodes(?vs0, nx) &*& vs == cons(v, vs0);

pred stack(list<i32> vs, *mut Stack s) =
    (*s).head |-> ?h &*& nodes(vs, h);

@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes(?vs, nodes);
//@ ens nodes(vs, nodes) &*& result == fold_left(plus, 0, vs);
{
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ open nodes(vs, nodes);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close nodes(vs, nodes);
    } else {
        //@ open nodes(vs, nodes);
        //@ close nodes(vs, nodes);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 &*& stack(nil, result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(nil, 0);
        //@ close stack(nil, stack);
        
        
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(?vs, stack);
    //@ ens stack(vs, stack) &*& result == (vs == nil);
    {
        //@ open stack(vs, stack);
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        //@ close stack(vs, stack);
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(?vs, stack);
    //@ ens stack(vs, stack) &*& result == fold_left(plus, 0, vs);
    {
        //@ open stack(vs, stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(vs, stack);
        
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(?vs, stack);
    //@ ens stack(cons(value, vs), stack);
    {
        //@ open stack(vs, stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(vs, (*n).next);
        //@ close nodes(cons(value, vs), n);
        //@ close stack(cons(value, vs), stack);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(cons(?v, ?vs0), stack);
    //@ ens stack(vs0, stack) &*& result == v;
    {
        //@ open stack(cons(v, vs0), stack);
        let head = (*stack).head;
        //@ open nodes(cons(v, vs0), head);
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(vs0, stack);
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
    //@ req stack(?vs, stack) &*& 0 <= n &*& n <= length(vs);
    //@ ens stack(drop(n, vs), stack);
    {
        let mut i = 0;
        loop {
            //@ inv stack(drop(i, vs), stack) &*& 0 <= i &*& i <= n;
            if i == n {
                break;
            }
            Stack::pop(stack);
            i += 1;
        }
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(?vs, stack);
    //@ ens true;
    {
        //@ open stack(vs, stack);
        let mut n = (*stack).head;
        loop {
            //@ inv nodes(?vsn, n);
            if n.is_null() {
                break;
            }
            //@ open nodes(vsn, n);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
        }
        //@ open nodes(?vsfin, n);
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
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