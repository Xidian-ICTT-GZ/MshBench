use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred nodes(n: *mut Node) =
    if n == 0 as *mut Node {
        true
    } else {
        alloc_block_Node(n) &*& struct_Node(n, ?next, ?value) &*& nodes(next)
    };

pred stack(s: *mut Stack) =
    alloc_block_Stack(s) &*& struct_Stack(s, ?head) &*& nodes(head);

@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ req nodes(node);
//@ ens nodes(node) &*& true;
unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node);
    }
    result
}

impl Stack {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0 as *mut Node);
        //@ close stack(stack);
        stack
    }

    //@ req stack(stack);
    //@ ens stack(stack) &*& true;
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes((*n).next);
        //@ close nodes(n);
        //@ close stack(stack);
    }

    //@ req stack(stack) &*& nodes(?head) &*& head != 0;
    //@ ens stack(stack) &*& true;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack);
        //@ open nodes((*stack).head);
        //@ assert false; // Stack::dispose requires empty stack; otherwise nodes leak.
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

        //@ open stack(s);
        //@ open nodes((*s).head);
        //@ close nodes(0 as *mut Node);
        //@ close stack(s);
        Stack::dispose(s);
    }
}