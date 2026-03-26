use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

predicate_node(?n: *mut Node; ?next: Option<*mut Node>; ?v: i32) =
    n->next |-> next &*& n->value |-> v &*& malloc_block_Node(n);

predicate_nodes(?n: *mut Node) =
    n == std::ptr::null_mut()
    ? true
    : exists<*mut Node,v>(predicate_node(n, option_some(?next), v) &*& predicate_nodes(next));

predicate_stack(?s: *mut Stack; ?nodes: *mut Node) =
    s->head |-> nodes &*& malloc_block_Stack(s) &*& predicate_nodes(nodes);

@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

//@ req predicate_nodes(n);
//@ ensures true;
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open predicate_node(n, option_some(?next), ?v);
        //@ open predicate_nodes(next);
        dispose_nodes((*n).next);
        //@ close predicate_nodes(n);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

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
    return stack;
}

//@ req predicate_stack(stack, ?nodes);
//@ ensures predicate_stack(stack, nodes) &*& result == (nodes == std::ptr::null_mut());
unsafe fn is_empty(stack: *mut Stack) -> bool
{
    let head = (*stack).head;

    let result = (*stack).head.is_null();

    return result;
}

//@ req predicate_stack(stack, ?nodes);
//@ ensures predicate_stack(stack, ?nodes0) &*&
//@     nodes0 == cons(?new_node, nodes) &*& predicate_node(new_node, option_some(nodes), value);
unsafe fn push(stack: *mut Stack, value: i32)
{
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    //@ close predicate_node(n, option_some((*stack).head), value);
    (*stack).head = n;
    //@ close predicate_stack(stack, n);
}

//@ req predicate_stack(stack, ?nodes) &*& nodes != std::ptr::null_mut();
//@ ensures predicate_stack(stack, ?tail) &*& tail == (*nodes).next &*& result == (*nodes).value;
unsafe fn pop(stack: *mut Stack) -> i32
{
    let head = (*stack).head;
    //@ open predicate_stack(stack, nodes);
    //@ open predicate_node(head, option_some(?next), ?v);
    let result = (*head).value;
    (*stack).head = (*head).next;
    //@ close predicate_stack(stack, (*head).next);
    //@ close predicate_nodes((*head).next);
    dealloc(head as *mut u8, Layout::new::<Node>());

    return result;
}

//@ req predicate_stack(stack, ?nodes);
//@ ensures true;
unsafe fn dispose(stack: *mut Stack)
{
    //@ open predicate_stack(stack, nodes);
    dispose_nodes((*stack).head);
    dealloc(stack as *mut u8, Layout::new::<Stack>());
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