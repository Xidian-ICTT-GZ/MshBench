unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes |-> ?node_opt &*& node_opt.is_some() ? node_ptr : true &*& node_ptr.is_null() ? true : node_ptr |-> ?node &*& node.next |-> ?next &*& node.value |-> ?val &*& own_node_fields(node_ptr, next, val);
//@ ens nodes |-> ?node_opt2 &*& node_opt2.is_some() ? node_ptr2 : true &*& node_ptr2.is_null() ? true : node_ptr2 |-> ?node2 &*& node2.next |-> ?next2 &*& node2.value |-> ?val2 &*& own_node_fields(node_ptr2, next2, val2);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open own_node_fields(nodes, _, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close own_node_fields(nodes, (*nodes).next, (*nodes).value);
    }

    result
}

/*@
pred_ctor node_pred(node: *mut Node, next: *mut Node, value: i32)() = 
    node |-> { next: next, value: value };
pred own_node_fields(node: *mut Node, next: *mut Node, value: i32) = 
    [_]is_node_pred(node, node_pred) &*& node_pred(node, next, value)();
@*/

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack |-> ?stack_obj &*& stack_obj.head |-> ?head &*& own_stack_fields(stack, head);
    //@ ens stack |-> ?stack_obj2 &*& stack_obj2.head |-> ?head2 &*& own_stack_fields(stack, head2);
    {
        //@ open own_stack_fields(stack, (*stack).head);
        let result = get_nodes_sum((*stack).head);
        //@ close own_stack_fields(stack, (*stack).head);
        result
    }
}

/*@
pred_ctor stack_pred(stack: *mut Stack, head: *mut Node)() = 
    stack |-> { head: head };
pred own_stack_fields(stack: *mut Stack, head: *mut Node) = 
    [_]is_stack_pred(stack, stack_pred) &*& stack_pred(stack, head)();
@*/