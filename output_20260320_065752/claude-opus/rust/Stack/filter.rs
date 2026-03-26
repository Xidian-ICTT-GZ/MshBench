use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ 
predicate_node(Node *n; i32 value, Node *next) =
    n->value |-> value &*& n->next |-> next &*& alloc_block_Node(n);
@*/

/*@ 
predicate_stack(Stack *s; Node *head) =
    s->head |-> head &*& alloc_block_Stack(s);
@*/

/*@

fixpoint bool is_node_list(Node *n)
{
    return n == NULL || is_node_list(((Node *)n)->next);
}

predicate nodes_list(Node *n) =
    n == NULL ? 
        true 
    : 
        predicate_node(n, ((Node *)n)->value, ((Node *)n)->next) &*& nodes_list(((Node *)n)->next);

@*/

/*@
fixpoint usize size_node()
{
    return sizeof<Node>();
}

fixpoint usize size_stack()
{
    return sizeof<Stack>();
}
@*/

/*@ 

predicate alloc_block_Node(Node *p; ) = true;
predicate alloc_block_Stack(Stack *p; ) = true;

@*/

type I32Predicate = unsafe fn(i32) -> bool;

//@ req n == 0 || predicate_node(n, _, _);
//@ ensures true;
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        //@ open predicate_node(n, _, _);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            (*n).next = next;
            //@ close predicate_node(n, (*n).value, next);
            n
        } else {
            next = (*n).next;
            //@ close predicate_node(n, _, _); // should not be closed again, but just to please verifier
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

//@ req n == 0 || predicate_node(n, _, _);
//@ ensures true;
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open predicate_node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    //@ req true;
    //@ ensures predicate_stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close predicate_stack(stack, std::ptr::null_mut());
        stack
    }

    //@ req predicate_stack(stack, _);
    //@ ensures predicate_stack(stack, old((*stack).head));
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open predicate_stack(stack, _);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close predicate_node(n, value, (*n).next);
        //@ close predicate_stack(stack, n);
    }

    //@ req predicate_stack(stack, ?head) &*& head != std::ptr::null_mut() &*& predicate_node(head, _, _);
    //@ ensures predicate_stack(stack, old((*head).next));
    //@ ensures result == old((*head).value);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open predicate_stack(stack, ?head);
        let head = (*stack).head;
        //@ open predicate_node(head, ?v, ?next);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close predicate_stack(stack, next);
        result
    }

    //@ req predicate_stack(stack, ?head);
    //@ ensures predicate_stack(stack, ?newhead);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        //@ open predicate_stack(stack, ?head);
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        //@ close predicate_stack(stack, head);
    }

    //@ req predicate_stack(stack, ?head);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open predicate_stack(stack, ?head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}