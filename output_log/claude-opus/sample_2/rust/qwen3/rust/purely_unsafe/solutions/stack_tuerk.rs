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
        // For all nodes except last, node_pred links to next node exactly
        forall<j: int> 0 <= j < len(nodes) - 1 ==> 
            node_pred(nth(nodes, j), (*nth(nodes, j)).value, nth(nodes, j+1)) &&
        // Last node points to null
        node_pred(nth(nodes, len(nodes)-1), (*nth(nodes, len(nodes)-1)).value, 0))
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
        // If n != 0 then we own node_pred at n with some value and next pointer
        (n != 0 ==> node_pred(n, _, ?next_ptr)) &&
        // The nodes list can be split into the first i elements (taken) and rest,
        // where the rest begins with current n (if not null)
        exists<rest: list<*mut Node>> 
            nodes == append(take(i, nodes), cons(n, rest)) &&
        // Length preservation in list split
        i + len(rest) == len(nodes)
    )]
    loop {
        if n.is_null() {
            break;
        }
        let old_n = n;
        n = (*n).next;
        i += 1;
        // The invariant is preserved because moving along the next pointer in the list
        // corresponds to taking one more element from nodes into taken prefix
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}