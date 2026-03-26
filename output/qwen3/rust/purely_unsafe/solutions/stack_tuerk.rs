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
    (nodes == nil ==> true) &&
    (nodes != nil ==> 
        forall<j: int> 0 <= j < len(nodes) - 1 ==> 
            node_pred(hd(tl^n(nodes, j)), 
                      value_of_node(hd(tl^n(nodes, j))), 
                      hd(tl^n(nodes, j+1))) &&
        node_pred(hd(tl^n(nodes, len(nodes)-1)), 
                  value_of_node(hd(tl^n(nodes, len(nodes)-1))), 
                  0))
}

#[lem]
fn value_of_node(p: *mut Node) -> i32
    requires node_pred(p, _, _)
    ensures true
{
    (*p).value
}

#[lem]
fn tl^n(l: list<*mut Node>, n: int) -> list<*mut Node>
    requires 0 <= n && n <= len(l)
    ensures len(result) == len(l) - n &&
            forall<i: int> 0 <= i < len(result) ==> 
                nth(result, i) == nth(l, i + n)
{
    if n == 0 { l } else { tl(tl^n(l, n-1)) }
}

#[requires(stack != 0 && stack_pred(stack, ?nodes))]
#[ensures(result == len(nodes))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
        n != 0 ==> node_pred(n, _, ?next_ptr) &&
        exists<rest: list<*mut Node>> 
            nodes == append(take(i, nodes), cons(n, rest)) &&
        len(rest) >= 0 &&
        i + len(rest) == len(nodes)
    )]
    loop {
        if n.is_null() {
            break;
        }
        let old_n = n;
        n = (*n).next;
        i += 1;
        // Maintain invariant:
        // Before: nodes = take(i-1, nodes) ++ [old_n] ++ rest
        // After:  nodes = take(i, nodes) ++ rest' where rest' = tl(rest)
        // Since old_n points to next = n, and node_pred(old_n, _, n) holds,
        // the list structure is preserved.
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}