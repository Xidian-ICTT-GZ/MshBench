//@ pred Node(node: *mut Node; next: *mut Node, value: i32) = node |-> ?n &*& n.next |-> next &*& n.value |-> value;
//@ pred Nodes(nodes: *mut Node;) =
//@   nodes == null ?
//@     true
//@   :
//@     Node(nodes, ?next, ?value) &*& Nodes(next);
//@ pred Stack(stack: *mut Stack; head: *mut Node) = stack |-> ?s &*& s.head |-> head;
//@ pred Stacks(stack: *mut Stack;) = Stack(stack, ?head) &*& Nodes(head);

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes);
//@ ens Nodes(nodes) &*& result == sum_nodes(nodes);
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes);
        //@ open Node(nodes, _, _);
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
        //@ close Node(nodes, (*nodes).next, (*nodes).value);
        //@ close Nodes(nodes);
    }

    result
}

//@ fixpoint i32 sum_nodes(*mut Node nodes) {
//@   match nodes {
//@     null => 0,
//@     _ => sum_nodes((*(nodes)).next) + (*(nodes)).value
//@   }
//@ }

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req Stacks(stack);
    //@ ens Stacks(stack) &*& result == sum_nodes((*stack).head);
    {

        //@ open Stacks(stack);
        let result = get_nodes_sum((*stack).head);
        //@ close Stacks(stack);

        result
    }
}