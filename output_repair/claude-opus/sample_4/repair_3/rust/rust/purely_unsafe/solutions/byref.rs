use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

/*@

pred Node(n: *mut Node; next: *mut Node, value: i32) =
    (*n).next |-> next &*& (*n).value |-> value &*& alloc_block(n as *mut u8, Layout::new_::<Node>());

pred Nodes(n: *mut Node;) =
    if n == 0 as *mut Node {
        true
    } else {
        Node(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>());

pred StackOwns(s: *mut Stack;) =
    Stack(s, ?head) &*& Nodes(head);

pred NodeRef(p: *mut *mut Node; n: *mut Node) =
    *p |-> n;

pred I32Pred(p: I32Predicate;) = true;

@*/

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req NodeRef(n, ?node) &*& Nodes(node) &*& I32Pred(p);
//@ ens NodeRef(n, ?new_node) &*& Nodes(new_node) &*& I32Pred(p);
{
    //@ open NodeRef(n, node);
    if !(*n).is_null() {
        //@ open Nodes(node);
        //@ open Node(node, ?next, ?val);
        let keep = p((**n).value);
        if keep {
            //@ close Node(node, next, val);
            let next_ptr = &raw mut (**n).next;
            //@ close NodeRef(next_ptr, next);
            filter_nodes(next_ptr, p);
            //@ open NodeRef(next_ptr, ?new_next);
            //@ close Node(node, new_next, val);
            //@ close Nodes(node);
            //@ close NodeRef(n, node);
        } else {
            let next_ = (**n).next;
            //@ close Node(node, next, val);
            //@ open Node(node, next, val);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close NodeRef(n, next_);
            filter_nodes(n, p);
        }
    } else {
        //@ close Nodes(node);
        //@ close NodeRef(n, node);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req Nodes(n);
//@ ens true;
{
    if !n.is_null() {
        //@ open Nodes(n);
        //@ open Node(n, ?next, ?val);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open Nodes(n);
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens StackOwns(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Stack(stack, 0 as *mut Node);
        //@ close Nodes(0 as *mut Node);
        //@ close StackOwns(stack);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req StackOwns(stack);
    //@ ens StackOwns(stack);
    {
        //@ open StackOwns(stack);
        //@ open Stack(stack, ?head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node(n, head, value);
        //@ close Nodes(n);
        //@ close Stack(stack, n);
        //@ close StackOwns(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req StackOwns(stack) &*& Stack(stack, ?head) &*& head != 0 as *mut Node;
    //@ ens StackOwns(stack);
    {
        //@ open StackOwns(stack);
        //@ open Stack(stack, head);
        let head = (*stack).head;
        //@ open Nodes(head);
        //@ open Node(head, ?next, ?val);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        //@ close Stack(stack, next);
        //@ close StackOwns(stack);
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req StackOwns(stack) &*& I32Pred(p);
    //@ ens StackOwns(stack) &*& I32Pred(p);
    {
        //@ open StackOwns(stack);
        //@ open Stack(stack, ?head);
        let head_ptr = &raw mut (*stack).head;
        //@ close NodeRef(head_ptr, head);
        filter_nodes(head_ptr, p);
        //@ open NodeRef(head_ptr, ?new_head);
        //@ close Stack(stack, new_head);
        //@ close StackOwns(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req StackOwns(stack);
    //@ ens true;
    {
        //@ open StackOwns(stack);
        //@ open Stack(stack, ?head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens true;
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ close I32Pred(neq_20);
        Stack::filter(s, neq_20);
        //@ open I32Pred(neq_20);
        Stack::dispose(s);
    }
}