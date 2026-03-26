unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes |-> ?n &*& n.is_null() ? true : node(n, ?val, ?next) &*& get_nodes_sum(next) |-> ?next_sum &*& next_sum == 0;
//@ ens nodes |-> ?n &*& n.is_null() ? true : node(n, ?val, ?next) &*& get_nodes_sum(next) |-> ?next_sum &*& next_sum == 0;
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open node(nodes, _, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close node(nodes, _, _);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack |-> ?head &*& get_nodes_sum(head) |-> ?sum &*& sum == 0;
    //@ ens stack |-> ?head &*& get_nodes_sum(head) |-> ?sum &*& sum == 0;
    {

        let result = get_nodes_sum((*stack).head);

        result
    }
}