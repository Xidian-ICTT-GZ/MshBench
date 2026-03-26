/*@ pred Stack(node: *mut Stack, head: *mut Node) = 
  alloc_block_Stack(node) &*& 
  struct_Stack_padding(node) &*& 
  (*node).head |-> head &*& 
  Nodes(head); 
@*/

/*@ pred Nodes(node: *mut Node) = 
  node == std::ptr::null_mut() ? 
    true 
  : 
    alloc_block_Node(node) &*& 
    struct_Node_padding(node) &*& 
    (*node).next |-> ?next &*& 
    Nodes(next); 
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req Stack(stack, ?head);
//@ ens Stack(stack, head) &*& result == length_nodes(head);
{
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open Stack(stack, head);
    //@ assert (*stack).head |-> n &*& Nodes(n);
    loop 
    //@ inv Nodes(n) &*& i == length_nodes_from(n, head) - length_nodes(n);
    {
        if n.is_null() {
            break;
        }
        //@ open Nodes(n);
        n = (*n).next;
        i += 1;
        //@ close Nodes(n);
    }
    //@ close Stack(stack, head);
    i
}

/*@ fix length_nodes(n: *mut Node) -> i32 {
  match n == std::ptr::null_mut() {
    true => 0,
    false => 1 + length_nodes((*(n)).next)
  }
} @*/

/*@ fix length_nodes_from(cur: *mut Node, orig: *mut Node) -> i32 {
  length_nodes(orig) - length_nodes(cur)
} @*/