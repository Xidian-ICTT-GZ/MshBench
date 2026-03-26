use std::ptr;

/*@

pred StackNode(node: *mut StackNode; next: *mut StackNode) =
    (*node).next |-> next;

pred stack_node_list(p: *mut StackNode, len: i32) =
    if p == 0 {
        len == 0
    } else {
        StackNode(p, ?next) &*& stack_node_list(next, ?rest) &*& len == rest + 1
    };

pred Stack(stack: *mut Stack; head: *mut StackNode) =
    (*stack).head |-> head;

@*/

struct StackNode {
    next: *mut StackNode,
}

struct Stack {
    head: *mut StackNode,
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack, ?head) &*& stack_node_list(head, ?len);
//@ ens Stack(stack, head) &*& stack_node_list(head, len) &*& result == len;
{
    //@ open Stack(stack, head);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close Stack(stack, head);
    
    loop
    //@ inv stack_node_list(n, ?remaining) &*& i + remaining == len &*& i >= 0;
    {
        //@ open stack_node_list(n, remaining);
        if n.is_null() {
            break;
        }
        let next = (*n).next;
        //@ close StackNode(n, next);
        i += 1;
        n = next;
        //@ leak StackNode(_, _);
    }

    i
}