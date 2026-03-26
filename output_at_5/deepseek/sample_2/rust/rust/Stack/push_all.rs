use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate nodes(n: *mut Node; count: int) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        alloc_block_Node(n) &*& struct_Node_padding(n) &*&
        (*n).next |-> ?next &*& (*n).value |-> ?value &*&
        nodes(next, ?c) &*& count == c + 1
    };

predicate Stack(stack: *mut Stack) =
    alloc_block_Stack(stack) &*& struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*& nodes(head, _);
@*/

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens Stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close nodes(0 as *mut Node, 0);
        //@ close Stack(stack);
        (*stack).head = std::ptr::null_mut();
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        //@ open nodes(head, _);
        loop {
            //@ open nodes(n, _);
            if n.is_null() {
                //@ close nodes(n, 0);
                break;
            }
            n = (*n).next;
            i += 1;
        }
        //@ close nodes(head, _);
        //@ close Stack(stack);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack(stack) &*& Stack(other);
    //@ ens Stack(stack);
    {
        //@ open Stack(other);
        let head0 = (*other).head;
        //@ open nodes(head0, _);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            loop {
                //@ open nodes(n, _);
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            //@ open Stack(stack);
            (*n).next = (*stack).head;
            (*stack).head = head0;
            //@ close Stack(stack);
        } else {
            //@ close nodes(head0, 0);
            //@ open Stack(stack);
            //@ close Stack(stack);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack(stack);
    //@ ens Stack(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open Stack(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, ?count);
        //@ close Stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack(stack) &*& (*stack).head != 0 as *mut Node;
    //@ ens Stack(stack);
    {
        //@ open Stack(stack);
        let head = (*stack).head;
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack(stack);
    //@ ens true;
    {
        //@ open Stack(stack);
        //@ open nodes((*stack).head, _);
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