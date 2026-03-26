#[pred]
struct node_pred(p: *mut Node, value: i32, next: *mut Node) {
    p != 0 && 
    points_to(p, Node { next: next, value: value })
}

#[pred]
struct stack_pred(s: *mut Stack, nodes: list<*mut Node>) {
    s != 0 &&
    points_to(s, Stack { head: if nodes == nil then 0 else hd(nodes) }) &&
    // Non-empty nodes form a linked list of node_pred predicates
    (nodes == nil ==> true) &&
    (nodes != nil ==>
        node_pred(hd(nodes), _, if tl(nodes) == nil then 0 else hd(tl(nodes))) &&
        // all consecutive pairs in nodes linked properly by node_pred
        (
            forall<j: int> 0 <= j < len(nodes) - 1 ==>
                node_pred(nth(nodes, j), _, nth(nodes, j+1))
        ) &&
        node_pred(nth(nodes, len(nodes)-1), _, 0)
    )
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
            forall<i: int> 0 <= i < len(result) ==> nth(result, i) == nth(l, i + n)
{
    if n == 0 { l } else { tl(tl^n(l, n-1)) }
}

#[requires(stack != 0 && stack_pred(stack, ?nodes))]
#[ensures(result == len(nodes))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
        stack_pred(stack, nodes) &&
        // At each iteration, i counts nodes seen so far, n points to current node:
        // The nodes list is split as take(i, nodes) ++ rest
        // If n != 0, then n must be the head of rest
        (n == 0 ==> nodes == take(i, nodes)) &&
        (n != 0 ==> 
            node_pred(n, _, ?next_ptr) &&
            rest: list<*mut Node> &*&
            nodes == append(take(i, nodes), cons(n, rest)) &&
            len(rest) >= 0 &&
            (rest == nil ==> n == 0) &&
            (rest != nil ==> next_ptr == hd(rest))
        )
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