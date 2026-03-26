use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Node_pred(node: *mut Node; next: *mut Node, value: i32) =
    (*node).next |-> next &*& (*node).value |-> value;

pred Stack_pred(stack: *mut Stack; head: *mut Node) =
    (*stack).head |-> head;

pred List(head: *mut Node;) =
    if head == std::ptr::null_mut() {
        true
    } else {
        Node_pred(head, ?next, ?value) &*& List(next)
    };

lem List_append(head: *mut Node)
    req List(head) &*& head != std::ptr::null_mut() &*& Node_pred(?last, std::ptr::null_mut(), ?v) &*& List(?tail);
    ens List(head);
{
    open List(head);
    if head == std::ptr::null_mut() {
    } else {
        open Node_pred(head, ?next, ?value);
        if next == std::ptr::null_mut() {
            close Node_pred(head, next, value);
            close List(head);
        } else {
            close Node_pred(head, next, value);
            List_append(next);
            close List(head);
        }
    }
}
@*/

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req Layout::new::<Stack>().size() > 0;
    //@ ens Stack_pred(result, std::ptr::null_mut()) &*& List(std::ptr::null_mut());
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close List(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close Stack_pred(stack, std::ptr::null_mut());
        stack
    }

    unsafe fn get_count(stack: *mut Stack) -> i32
    //@ req Stack_pred(stack, ?head) &*& List(head);
    //@ ens Stack_pred(stack, head) &*& List(head) &*& result >= 0;
    {
        //@ open Stack_pred(stack, head);
        let head = (*stack).head;
        //@ close Stack_pred(stack, head);

        let mut n = head;
        let mut i: i32 = 0;

        loop
        //@ inv List(n) &*& i >= 0;
        {
            //@ open List(n);
            if n.is_null() {
                //@ close List(n);
                break;
            }
            //@ open Node_pred(n, ?next_n, ?val);
            n = (*n).next;
            //@ close Node_pred(old_n, next_n, val);
            //@ close List(old_n);
            i += 1;
        }

        //@ close List(head);
        i
    }

    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    //@ req Stack_pred(stack, ?h1) &*& List(h1) &*& Stack_pred(other, ?h2) &*& List(h2);
    //@ ens Stack_pred(stack, ?new_head) &*& List(new_head);
    {
        //@ open Stack_pred(other, h2);
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        //@ open List(head0);
        if !n.is_null() {
            //@ close List(head0);
            loop
            //@ inv n != std::ptr::null_mut() &*& List(n);
            {
                //@ open List(n);
                //@ open Node_pred(n, ?next_n, ?val);
                if (*n).next.is_null() {
                    //@ open Stack_pred(stack, h1);
                    (*n).next = (*stack).head;
                    //@ close Node_pred(n, h1, val);
                    //@ close List(n);
                    (*stack).head = head0;
                    //@ close Stack_pred(stack, head0);
                    break;
                }
                let next = (*n).next;
                //@ close Node_pred(n, next_n, val);
                //@ close List(n);
                n = next;
            }
        } else {
            //@ close List(std::ptr::null_mut());
        }
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req Stack_pred(stack, ?h) &*& List(h) &*& Layout::new::<Node>().size() > 0;
    //@ ens Stack_pred(stack, ?n) &*& List(n);
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ open Stack_pred(stack, h);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close Node_pred(n, h, value);
        //@ close List(n);
        (*stack).head = n;
        //@ close Stack_pred(stack, n);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req Stack_pred(stack, ?h) &*& List(h) &*& h != std::ptr::null_mut();
    //@ ens Stack_pred(stack, ?tail) &*& List(tail);
    {
        //@ open Stack_pred(stack, h);
        let head = (*stack).head;
        //@ open List(head);
        //@ open Node_pred(head, ?tail, ?v);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_pred(stack, tail);

        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req Stack_pred(stack, ?h) &*& List(h) &*& h == std::ptr::null_mut();
    //@ ens true;
    {
        //@ open Stack_pred(stack, h);
        //@ open List(h);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let _ = Stack::pop(s);
        let _ = Stack::pop(s);
        Stack::dispose(s);
    }
}