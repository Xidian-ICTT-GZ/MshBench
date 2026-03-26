use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@

pred nodes(node: *mut Node; count: i32) =
    node == 0 ?
        count == 0
    :
        count > 0 &*&
        alloc_block_Node(node) &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?v &*&
        nodes(next; count - 1);

pred stack(stack: *mut Stack; count: i32) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?head &*&
    nodes(head; count);

@*/

impl Stack {

    //@ req true;
    //@ ens result != 0 &*& stack(result, 0);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close alloc_block_Stack(stack);
        //@ close stack(stack, 0);
        (*stack).head = std::ptr::null_mut();

        //@ open stack(stack, 0);
        //@ close stack(stack, 0);
        stack
    }

    //@ req stack(stack, ?count);
    //@ ens stack(stack, count + 1);
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close alloc_block_Node(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n, count + 1);
        (*stack).head = n;
        //@ close stack(stack, count + 1);
    }

    //@ req stack(stack, ?count) &*& count > 0;
    //@ ens stack(stack, count - 1);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, count);
        let head = (*stack).head;
        //@ open nodes(head, count);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open alloc_block_Node(head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, count - 1);
        result
    }

    //@ req stack(stack, ?count);
    //@ ens stack(stack, count);
    unsafe fn reverse(stack: *mut Stack)
    {
        //@ open stack(stack, count);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close nodes(m, 0);

        loop {
            //@ inv nodes(n, ?cn) &*& nodes(m, ?cm) &*& cn + cm == count;
            if n.is_null() {
                break;
            }

            //@ open nodes(n, cn);
            let next = (*n).next;

            (*n).next = m;
            //@ close nodes(n, cm + 1);
            m = n;
            n = next;
        }

        //@ open nodes(n, ?cn_end);
        //@ assert cn_end == 0;
        (*stack).head = m;
        //@ close stack(stack, count);
    }

    //@ req stack(stack, ?count);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, count);
        //@ open nodes((*stack).head, count);
        //@ assume_correct
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        //@ open stack(s, 0);
        //@ close stack(s, 0);
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}