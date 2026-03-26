use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ 
predicate node(struct Node* n; int v, struct Node* next) =
    n->value |-> v &*& n->next |-> next;

predicate stack(struct Stack* s; struct Node* head) =
    s->head |-> head;

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
    //@ ens stack(result, null);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, null);
        stack
    }

    //@ req stack(stack, ?head);
    //@ ensures stack(stack, ?new_head) &*& (head == null ? true : node(head, ?v, ?next) &*& new_head == ?x);
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

    //@ req stack(stack, ?head) &*& head != std::ptr::null_mut();
    //@ ensures stack(stack, ?new_head) &*& node(head, result, new_head);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, ?head);
        let head = (*stack).head;
        //@ open node(head, ?v, ?next);

        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ close stack(stack, next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    //@ req stack(stack, ?head);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, ?head);
        //@ if head != std::ptr::null_mut() {
        //@   leak node(head, _, _);
        //@ }
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