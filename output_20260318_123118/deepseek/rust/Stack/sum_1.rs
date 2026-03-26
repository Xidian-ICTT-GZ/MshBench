use vstd::prelude::*;

verus! {

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_valid(n: *mut Node) -> bool
    reads n
    ensures result ==>
        addr_of!((*n).value).is_nonoverlapping_with(addr_of!((*n).next)) &&
        (*n).value.is_constant()
{
    !n.is_null() &&
    &&& (*n).value.is_constant()
    &&& (*n).next.is_constant()
}

predicate nodes_owned(n: *mut Node) -> bool
    reads n
    ensures result ==> node_valid(n)
{
    if n.is_null() {
        true
    } else {
        node_valid(n) && nodes_owned((*n).next)
    }
}

predicate stack_valid(s: *mut Stack) -> bool
    reads s
    ensures result ==>
        addr_of!((*s).head).is_nonoverlapping_with(s) &&
        (*s).head.is_constant()
{
    !s.is_null() &&
    &&& (*s).head.is_constant()
}

predicate stack_owned(s: *mut Stack) -> bool
    reads s
    ensures result ==> stack_valid(s)
{
    stack_valid(s) && nodes_owned((*s).head)
}

#[requires(nodes_owned(nodes))]
#[ensures(|result| nodes_owned(nodes))]
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    let mut result = 0;

    if !nodes.is_null() {
        proof {
            let nodes_ptr = nodes;
            assert(nodes_owned(nodes_ptr)) by {
                unfold(nodes_owned(nodes_ptr));
            }
        }
        
        let next_nodes = (*nodes).next;
        result = get_nodes_sum(next_nodes);
        
        proof {
            let nodes_ptr = nodes;
            assert(node_valid(nodes_ptr)) by {
                unfold(nodes_owned(nodes_ptr));
            }
        }
        
        result += (*nodes).value;
        
        proof {
            let nodes_ptr = nodes;
            fold(nodes_owned(nodes_ptr));
        }
    } else {
        proof {
            let nodes_ptr = nodes;
            fold(nodes_owned(nodes_ptr));
        }
    }

    result
}

impl Stack {
    #[requires(stack_owned(stack))]
    #[ensures(|result| stack_owned(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        proof {
            let stack_ptr = stack;
            assert(stack_owned(stack_ptr)) by {
                unfold(stack_owned(stack_ptr));
            }
        }
        
        let head_nodes = (*stack).head;
        let result = get_nodes_sum(head_nodes);
        
        proof {
            let stack_ptr = stack;
            fold(stack_owned(stack_ptr));
        }
        
        result
    }
}

}