/*@ 
pred node(?n: int, *nodes: ptr) =
    nodes != 0 &*& 
    malloc_block_node(nodes) &*& 
    (*nodes).value |-> n &*& 
    (*nodes).next |-> ?next &*& 
    (next == 0 ? true : node(?m, next));

fixpoint int nodes_sum(predicate (int) p, list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return x + nodes_sum(p, xs0);
    }
}
@*/
#[repr(C)]
struct Node {
    value: i32,
    next: *mut Node,
}

/*@ 
pred stack(?s:list<int>, *st: ptr) = 
    st != 0 &*& malloc_block_stack(st) &*& 
    (*st).head |-> ?head &*& node_list(head, s);

pred node_list(*nodes: ptr, list<int> xs) = 
    nodes == 0 ? xs == nil : 
    node(?v, nodes) &*& (*nodes).next |-> ?next &*& node_list(next, ?rest) &*& xs == cons(v, rest);

@*/
#[repr(C)]
struct Stack {
    head: *mut Node,
}

//@ req nodes == 0 || node_list(nodes, ?ns);
//@ ens nodes == 0 || node_list(nodes, ?ns);
//@ ens true;
//@ ensures result == foldl(|acc, x| acc + x, 0, ns);
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req nodes == 0 || node_list(nodes, ?ns);
//@ ens nodes == 0 || node_list(nodes, ns);
//@ ensures result == foldl(|acc, x| acc + x, 0, ns);
{
    let mut result = 0;
    if !nodes.is_null() {
        //@ open node(?v, nodes);
        //@ open node_list((*nodes).next, ?rest);
        result = get_nodes_sum((*nodes).next);
        //@ open node_list((*nodes).next, rest);
        //@ assert v: i32;
        result += (*nodes).value;
        //@ close node_list(nodes, cons((*nodes).value, rest));
        //@ close node((*nodes).value, nodes);
    }
    result
}

impl Stack {
    //@ req stack != 0 &*& stack(?lst, stack);
    //@ ensures stack(?lst, stack);
    //@ ensures result == foldl(|acc, x| acc + x, 0, lst);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack != 0 &*& stack(?lst, stack);
    //@ ensures stack(lst, stack);
    //@ ensures result == foldl(|acc, x| acc + x, 0, lst);
    {
        //@ open stack(?lst, stack);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(lst, stack);
        result
    }
}