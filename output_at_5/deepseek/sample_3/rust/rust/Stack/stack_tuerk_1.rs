unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req [?q]stack->?s &*& stack_slice(s, ?nodes);
//@ ens [q]stack->s &*& stack_slice(s, nodes) &*& result == length(nodes);
{
    //@ open stack_slice(s, nodes);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ let mut current_nodes = nodes;
    loop
    //@ inv [q]stack->s &*& stack_node_slice(n, current_nodes) &*& i == length(nodes) - length(current_nodes);
    {
        //@ open stack_node_slice(n, current_nodes);
        if n.is_null() {
            //@ close stack_node_slice(n, current_nodes);
            break;
        }
        //@ open stack_node(_);
        n = (*n).next;
        i += 1;
        //@ current_nodes = tail(current_nodes);
        //@ close stack_node_slice(n, current_nodes);
    }
    //@ close stack_slice(s, nodes);
    i
}