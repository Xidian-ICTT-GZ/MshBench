/*@ pred node(node: *mut Node, value: i32, next: *mut Node) = 
  alloc_block_node(node) &*& 
  struct_Node_padding(node) &*& 
  (*node).value |-> value &*& 
  (*node).next |-> next;
@*/

/*@ pred nodes(node: *mut Node, values: list<i32>) =
  match values {
    nil => node == null(),
    cons(v, vs) => node != null() &*& 
                   node(node, v, ?next) &*& 
                   nodes(next, vs)
  };
@*/

/*@ pred stack(s: *mut Stack, values: list<i32>) =
  alloc_block_Stack(s) &*& 
  struct_Stack_padding(s) &*& 
  (*s).head |-> ?h &*& 
  nodes(h, values);
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node, ?vs);
//@ ens nodes(node, vs) &*& result == sum(vs);
{
    let mut result = 0;
    //@ open nodes(node, vs);
    if !node.is_null() {
        //@ assert node(node, ?v, ?next) &*& nodes(next, ?tail_vs);
        let tail_sum = get_nodes_sum((*node).next);
        //@ close nodes(node, cons(v, tail_vs));
        result = (*node).value + tail_sum;
    } else {
        //@ close nodes(node, nil);
    }
    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, vs) &*& result == sum(vs);
    {
        //@ open stack(stack, vs);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, vs);
        result
    }
}