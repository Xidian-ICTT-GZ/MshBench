use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@ 
predicate node(struct Node* n, i32 value, struct Node* next) = 
    n->value |-> value &*& n->next |-> next;
@*/

struct Stack {
    head: *mut Node,
}

/*@ 
predicate stack(struct Stack* s, struct Node* head) = 
    s->head |-> head;
@*/

/*@ 
fixpoint bool is_null<T>(T* p) = p == 0 as T*;
@*/

//@ req true;
//@ ens true;
unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ requires node == 0 as *mut Node ? true : node != 0 as *mut Node &*& node != std::ptr::null_mut();
//@ ensures true;
{
    let mut result = 0;
    if !node.is_null() {
        //@ open node(node, ?v, ?nx);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close node(node, v, nx);
    }
    result
}

impl Stack {

    //@ req true;
    //@ ensures result != 0 as *mut Stack &*& stack(result, 0 as *mut Node);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, 0 as *mut Node);
        stack
    }

    //@ req stack != 0 as *mut Stack &*& stack(stack, ?head);
    //@ ensures stack(stack, head) &*& result == get_nodes_sum(head);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, head);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, head);
        result
    }

    //@ req stack != 0 as *mut Stack &*& stack(stack, ?head);
    //@ ensures stack(stack, ?head2) &*& head2 == (old head as *mut Node);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, ?head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, value, head);
        //@ close stack(stack, n);
    }

    //@ req stack != 0 as *mut Stack &*& stack(stack, ?head) &*& head != 0 as *mut Node &*& node(head, ?v, ?next);
    //@ ensures stack(stack, next) &*& node(head, v, next);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, ?head);
        let head = (*stack).head;
        //@ open node(head, ?v, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack, next);
        //@ close node(head, v, next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    //@ req stack != 0 as *mut Stack &*& stack(stack, ?head) &*& (head == 0 as *mut Node);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, ?head);
        //@ assert head == 0 as *mut Node; // all nodes must be popped before dispose
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