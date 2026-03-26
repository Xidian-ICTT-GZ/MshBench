/*@ pred node(node: *mut Node; next: *mut Node, value: i32) =
    alloc_block_Node(node) &*& (*node).next |-> next &*& (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack; nodes: list<*mut Node>) =
    alloc_block_Stack(stack) &*& (*stack).head |-> ?head &*&
    nodes == if head == 0 { nil } else { cons(head, ?tail) } &*&
    nodes_list(head, tail);
@*/

/*@ fixpoint list<*mut Node> nodes_list(*mut Node head, list<*mut Node> tail);
    fixpoint bool is_valid_nodes_list(list<*mut Node> xs);
@*/

/*@ pred nodes_list(head: *mut Node, tail: list<*mut Node>) =
    match head {
        0 => tail == nil,
        _ => node(head, ?next, _) &*& nodes_list(next, tail)
    };
@*/

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let s = Stack::create();
        //@ open stack(s, _);
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}

unsafe fn get_nodes_sum(node: *mut Node) -> i32
{
    //@ req nodes_list(node, ?xs);
    //@ ens nodes_list(node, xs) &*& result == sum_values(xs);
    
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes_list(node, _);
        //@ open node(node, _, _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close node(node, (*node).next, (*node).value);
        //@ close nodes_list(node, cons(node, _));
    } else {
        //@ close nodes_list(0, nil);
    }
    
    result
}

impl Stack {

    //@ req true;
    //@ ens stack(result, nil);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, nil);
        
        stack
    }
    
    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, nodes) &*& result == sum_values(nodes);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, ?nodes);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, nodes);
        
        result
    }
    
    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, cons(?n, nodes));
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, nodes);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        (*stack).head = n;
        //@ close stack(stack, cons(n, nodes));
    }
    
    //@ req stack(stack, cons(?n, ?nodes));
    //@ ens stack(stack, nodes) &*& result == ?val &*& node(n, _, val);
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, cons(n, nodes));
        let head = (*stack).head;
        //@ open node(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, nodes);
        
        result
    }

    //@ req stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

/*@ fixpoint i32 sum_values(list<*mut Node> xs) {
    match xs {
        nil => 0,
        cons(h, t) => ?v + sum_values(t) // Note: VeriFast will infer v from node predicate
    }
} @*/