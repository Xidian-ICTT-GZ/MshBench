#[pred]
struct node_pred(
    p: *mut Node,
    value: i32,
    next: *mut Node
) {
    p != 0 && 
    points_to(p, Node { next: next, value: value })
}

#[pred]
struct stack_pred(
    s: *mut Stack,
    nodes: list<*mut Node>
) {
    s != 0 &&
    points_to(s, Stack { head: if nodes == nil then 0 else hd(nodes) }) &&
    (
        nodes == nil ? 
            emp
        :
            node_pred(hd(nodes), ?v, ?n) * 
            stack_nodes_pred(tl(nodes), n)
    )
}

#[pred]
stack_nodes_pred(list_ptrs: list<*mut Node>, start: *mut Node) {
    switch(list_ptrs) {
        case nil:
            start == 0 ? emp : false
        case cons(h, t):
            node_pred(h, ?v, ?next) &*& h == start &*&
            stack_nodes_pred(t, next)
    }
}

#[lem]
fn value_of_node(p: *mut Node) -> i32
    requires node_pred(p, _, _)
    ensures true
{
    (*p).value
}

#[requires(stack != 0 && stack_pred(stack, ?nodes))]
#[ensures(result == len(nodes))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
        stack_pred(stack, nodes) &*&
        n != 0 ?
            node_pred(n, _, ?next_ptr) &*&
            exists<list<*mut Node>>(?rest)
                nodes == append(take(i, nodes), cons(n, rest)) &*&
                stack_nodes_pred(rest, next_ptr)
        :
            nodes == take(i, nodes) &*& n == 0
    )]
    loop {
        if n.is_null() {
            break;
        }
        let old_n = n;
        n = (*n).next;
        i += 1;
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}