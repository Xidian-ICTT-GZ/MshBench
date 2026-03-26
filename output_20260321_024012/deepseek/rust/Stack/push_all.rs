use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens result != 0 as *mut Stack &*& StackOwned(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackOwned(stack);
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(stack);
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        loop {
            //@ open NodeOwned?(n);
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        //@ close StackOwned(stack);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req StackOwned(stack) &*& StackOwned(other);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(other);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            loop {
                //@ open NodeOwned?(n);
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            //@ open StackOwned(stack);
            (*n).next = (*stack).head;
            (*stack).head = head0;
            //@ close StackOwned(stack);
        } else {
            //@ open StackOwned(stack);
            //@ close StackOwned(stack);
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open StackOwned(stack);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close NodeOwned(n);
        //@ close StackOwned(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackOwned(stack);
    //@ ens StackOwned(stack);
    {
        //@ open StackOwned(stack);
        let head = (*stack).head;
        //@ open NodeOwned(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close StackOwned(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackOwned(stack);
    //@ ens true;
    {
        //@ open StackOwned(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

//@ predicate NodeOwned(struct Node *node) = node != 0 &*& (*node).next |-> ?next &*& (*node).value |-> ?value &*& NodeOwned?(next);
//@ predicate NodeOwned?(struct Node *node) = node == 0 ? true : NodeOwned(node);
//@ predicate StackOwned(struct Stack *stack) = stack != 0 &*& (*stack).head |-> ?head &*& NodeOwned?(head);

fn main()
//@ req true;
//@ ens true;
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