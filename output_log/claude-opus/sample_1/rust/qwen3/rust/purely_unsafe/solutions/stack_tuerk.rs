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
    (nodes == nil ==> emp) &&
    (nodes != nil ==> 
        node_chain(nodes))
}

#[pred]
node_chain(list: list<*mut Node>) {
    switch(list) {
        case nil: emp
        case cons(h, t): node_pred(h, _, if t == nil then 0 else hd(t)) &*& node_chain(t)
    }
}

#[lem]
fn value_of_node(p: *mut Node) -> i32
    requires node_pred(p, _, _)
    ensures true
{
    (*p).value
}

#[lem]
fn tl_n(l: list<*mut Node>, n: int) -> list<*mut Node>
    requires 0 <= n && n <= len(l)
    ensures len(result) == len(l) - n &&
            forall<i: int> 0 <= i < len(result) ==> 
                nth(result, i) == nth(l, i + n)
{
    if n == 0 { l } else { tl_n(tl(l), n - 1) }
}

#[requires(stack != 0 && stack_pred(stack, ?nodes))]
#[ensures(result == len(nodes))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
        stack_pred(stack, nodes) &*&
        (n != 0 ? node_pred(n, _, ?next_ptr) : emp) &*&
        nodes == append(take(i, nodes), n != 0 ? cons(n, tl_n(nodes, i + 1)) : nil) &*&
        0 <= i && i <= len(nodes)
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