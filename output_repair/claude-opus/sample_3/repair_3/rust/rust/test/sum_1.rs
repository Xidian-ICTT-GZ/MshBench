use std::ptr;

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes(ptr: *mut Node; sum: i32) =
    if ptr == 0 as *mut Node {
        sum == 0
    } else {
        (*ptr).value |-> ?v &*&
        (*ptr).next |-> ?next &*&
        Nodes(next, ?rest_sum) &*&
        sum == v + rest_sum
    };

pred StackPred(stack: *mut Stack; sum: i32) =
    (*stack).head |-> ?h &*&
    Nodes(h, sum);
@*/

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?sum);
//@ ens Nodes(nodes, sum) &*& result == sum;
{
    let mut result = 0;

    if !nodes.is_null() {
        //@ open Nodes(nodes, sum);
        //@ assert (*nodes).value |-> ?v &*& (*nodes).next |-> ?next &*& Nodes(next, ?rest_sum) &*& sum == v + rest_sum;
        result = get_nodes_sum((*nodes).next);
        //@ assert Nodes((*nodes).next, rest_sum) &*& result == rest_sum;
        result += (*nodes).value;
        //@ assert result == v + rest_sum &*& (*nodes).value |-> v &*& (*nodes).next |-> next;
        //@ close Nodes(nodes, sum);
    } else {
        //@ open Nodes(nodes, sum);
        //@ assert sum == 0;
        //@ close Nodes(nodes, sum);
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req StackPred(stack, ?sum);
    //@ ens StackPred(stack, sum) &*& result == sum;
    {
        //@ open StackPred(stack, sum);
        //@ assert (*stack).head |-> ?h &*& Nodes(h, sum);
        let result = get_nodes_sum((*stack).head);
        //@ assert Nodes((*stack).head, sum) &*& result == sum;
        //@ close StackPred(stack, sum);

        result
    }
}