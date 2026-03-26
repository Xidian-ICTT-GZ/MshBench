use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

//@ predicate nodes(?node, list<i32> vals) =
//@     if node == std::ptr::null_mut() {
//@         vals == []
//@     } else {
//@         Node* n = node;
//@         n->next |-> ?next &*& n->value |-> ?v &*& malloc_block_Node(n) &*& nodes(next, ?tail);
//@         vals == cons(v, tail);
//@     }

struct Stack {
    head: *mut Node,
}

//@ predicate stack(struct Stack* s, list<i32> vals) =
//@     s->head |-> ?h &*& malloc_block_Stack(s) &*& nodes(h, vals);

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires nodes(node, ?vals);
//@ ensures nodes(node, vals) &*& result == fold_left(0, vals, |acc: int, x: int| acc + x);
{
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node, vals);
        let tail_sum = get_nodes_sum((*node).next);
        //@ open nodes((*node).next, ?tail_vals);
        //@ assert vals == cons(?v, tail_vals);
        result = (*node).value + tail_sum;
        //@ close nodes(node, vals);
    }
    //@ else {
    //@   open nodes(node, vals);
    //@   assert vals == [];
    //@   close nodes(node, vals);
    //@ }
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ requires emp;
    //@ ensures stack(result, []);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut(), []);
        //@ close stack(stack, []);
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vals);
    //@ ensures stack(stack, vals) &*& result == fold_left(0, vals, |acc: int, x: int| acc + x);
    {
        //@ open stack(stack, vals);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, vals);
        result
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ requires stack(stack, ?vals);
    //@ ensures stack(stack, cons(value, vals));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open stack(stack, vals);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, cons(value, vals));
        //@ close stack(stack, cons(value, vals));
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ requires stack(stack, ?vals) &*& vals != [];
    //@ ensures stack(stack, tail(vals)) &*& result == head(vals);
    {
        //@ open stack(stack, vals);
        let head = (*stack).head;
        //@ open nodes(head, vals);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, tail(vals));
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ requires stack(stack, ?vals);
    //@ ensures emp;
    {
        //@ open stack(stack, vals);
        //@ open nodes((*stack).head, vals);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}