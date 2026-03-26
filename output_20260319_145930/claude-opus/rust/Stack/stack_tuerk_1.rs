/*@
pred Nodes(n: *mut Node, count: i32) =
    if n == 0 {
        count == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes(next, ?rest_count) &*&
        count == rest_count + 1
    };

pred Stack(stack: *mut Stack, count: i32) =
    alloc_block_Stack(stack) &*&
    (*stack).head |-> ?head &*&
    Nodes(head, count);
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred Nodes_iter(n: *mut Node, visited: i32, remaining: i32) =
    if n == 0 {
        remaining == 0
    } else {
        alloc_block_Node(n) &*&
        (*n).next |-> ?next &*&
        (*n).value |-> ?value &*&
        Nodes_iter(next, visited + 1, remaining - 1)
    };
@*/

//@ req Stack(stack, ?count);
//@ ens Stack(stack, count) &*& result == count;
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open Stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open Nodes(n, count);
    //@ close Nodes(n, count);
    loop {
        //@ inv Nodes(n, ?remaining) &*& i + remaining == count &*& i >= 0;
        if n.is_null() {
            //@ open Nodes(n, remaining);
            break;
        }
        //@ open Nodes(n, remaining);
        n = (*n).next;
        i += 1;
        //@ close Nodes(old_n, remaining);
    }
    //@ close Nodes(n, 0);
    //@ close Stack(stack, count);
    i
}