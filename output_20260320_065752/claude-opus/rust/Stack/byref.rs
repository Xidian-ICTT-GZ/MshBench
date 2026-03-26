use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ 
predicate node(struct Node *n; int value, struct Node *next) = 
    n->value |-> value &*& n->next |-> next &*& alloc_block_Node(n);
@*/

/*@ 
predicate stack(struct Stack *s; struct Node *head) =
    s->head |-> head &*& alloc_block_Stack(s) &*& list(head);
@*/

/*@ 
predicate list(struct Node *n;) =
    n == NULL ? true : node(n, ?v, ?next) &*& list(next);
@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req list(*n);
//@ ensures list(*n);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires *n |-> ?node_ptr &*& list(node_ptr);
    //@ ensures *n |-> ?final_node &*& list(final_node);
{
    if !(*n).is_null() {
        //@ open list(*n);
        let keep = p((**n).value);
        if keep {
            //@ open node(*n, _, _);
            filter_nodes(&raw mut (**n).next, p);
            //@ close node(*n, (**n).value, (**n).next);
        } else {
            let next_ = (**n).next;
            //@ open node(*n, _, _);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            //@ close list(*n);
            return;
        }
        //@ close list(*n);
    }
    //@ close list(*n);
}

//@ req list(n);
//@ ensures true;
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open list(n);
        dispose_nodes((*n).next);
        //@ open node(n, _, _);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

//@ req true;
//@ ensures stack(result, NULL);
impl Stack {
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, NULL);
        stack
    }

    //@ req stack(stack, ?head);
    //@ ensures stack(stack, cons(?v, head));
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, value, (*n).next);
        //@ open stack(stack, ?head0);
        //@ close stack(stack, n);
    }

    //@ req stack(stack, cons(?v, ?tail));
    //@ ensures stack(stack, tail);
    //@ ensures result == v;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        //@ open stack(stack, head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open node(head, result, (*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, (*stack).head);
        result
    }

    //@ req stack(stack, ?head);
    //@ ensures stack(stack, ?filteredHead);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open stack(stack, head);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack(stack, (*stack).head);
    }

    //@ req stack(stack, ?head);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, ?head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}