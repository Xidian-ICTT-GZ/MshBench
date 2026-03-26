/*@

pred stack_node(node: *mut StackNode, next: *mut StackNode) =
    node != std::ptr::null_mut() &*&
    alloc_block(node, std::mem::size_of::<StackNode>()) &*&
    (*node).next |-> next;

pred stack_nodes(node: *mut StackNode) =
    if node == std::ptr::null_mut() {
        true
    } else {
        stack_node(node, ?next) &*& stack_nodes(next)
    };

pred stack(stack: *mut Stack) =
    stack != std::ptr::null_mut() &*&
    alloc_block(stack, std::mem::size_of::<Stack>()) &*&
    (*stack).head |-> ?head &*&
    stack_nodes(head);

@*/

/*@

type StackNode = _;

type Stack = _;

@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack);
//@ ens stack(stack);
{
    //@ open stack(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close stack(stack);
    loop {
        //@ inv stack(stack) &*& stack_nodes(n);
        //@ open stack(stack);
        //@ assert (*stack).head |-> ?head &*& stack_nodes(head);
        //@ close stack(stack);

        if n.is_null() {
            //@ open stack_nodes(n);
            break;
        }
        //@ open stack_nodes(n);
        //@ open stack_node(n, ?next);
        n = (*n).next;
        //@ close stack_node(n /* dummy */, next); // cannot close; keep ownership in stack_nodes(next)
        //@ close stack_nodes(next);
        i += 1;
    }

    i
}