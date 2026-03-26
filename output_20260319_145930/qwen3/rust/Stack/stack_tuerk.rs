/*@ pred node(node: *mut Node, next: *mut Node, value: i32) =
    alloc_block_node(node) &*& (*node).next |-> next &*& (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, nodes: list<*mut Node>) =
    alloc_block_stack(stack) &*& (*stack).head |-> ?head &*&
    nodes == if head == null then nil else cons(head, ?tail) &*&
    nodes_list(head, tail);
@*/

/*@ pred nodes_list(curr: *mut Node, rest: list<*mut Node>) =
    match rest with
    | nil => curr == null
    | cons(n, ns) => node(curr, n, ?v) &*& nodes_list(n, ns)
    ;
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack, ?nodes);
//@ ens stack(stack, nodes) &*& result == length(nodes);
{
    
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open stack(stack, nodes);
    //@ assert (*stack).head |-> n;
    //@ close stack(stack, nodes);
    loop {
        //@ inv nodes_list(n, ?rest) &*& i == length(nodes) - length(cons(n, rest)) &*& stack(stack, nodes);
        //@ open stack(stack, nodes);
        //@ assert (*stack).head |-> _;
        //@ close stack(stack, nodes);
        
        if n.is_null() {
            
            break;
        }
        //@ open nodes_list(n, rest);
        n = (*n).next;
        i += 1;
        //@ close nodes_list(n, rest);
        
        
    }
    
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}