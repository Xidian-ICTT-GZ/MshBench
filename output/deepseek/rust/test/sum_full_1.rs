use vstd::prelude::*;

verus! {

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate nodes_list(node: *mut Node) -> bool
    decreases
{
    if node.is_null() {
        true
    } else {
        exists(|next: *mut Node| node-->Node {
            value: _,
            next: next
        } *&* nodes_list(next))
    }
}

predicate stack(stack: *mut Stack) -> bool {
    exists(|head: *mut Node| stack-->Stack {
        head: head
    } *&* nodes_list(head))
}

#[requires(stack(stack))]
#[ensures(|result| stack(stack))]
unsafe fn get_nodes_sum(node: *mut Node) -> i32
    decreases
{
    let mut result = 0;
    if !node.is_null() {
        proof {
            open nodes_list(node);
        }
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        proof {
            close nodes_list(node);
        }
    } else {
        proof {
            open nodes_list(node);
        }
    }

    result
}

impl Stack {
    #[requires(stack(stack))]
    #[ensures(|result| stack(stack))]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        proof {
            open stack(stack);
        }
        let result = get_nodes_sum((*stack).head);
        proof {
            close stack(stack);
        }

        result
    }
}

}