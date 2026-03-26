#[pred]
struct node_pred(
    p: *mut Node,
    value: i32,
    next: *mut Node
) {
    p != 0 &*& points_to(p, Node { next: next, value: value })
}

#[pred]
struct stack_pred(
    s: *mut Stack,
    nodes: list<*mut Node>
) {
    s != 0 &*&
    points_to(s, Stack { head: if nodes == nil then 0 else hd(nodes) }) &*&
    (nodes == nil ? true : 
        (nodes != nil &*&
            (forall<j: int>
                0 <= j &*& j < len(nodes) - 1 ==>
                    node_pred(nth(nodes, j),
                              value_of_node(nth(nodes, j)),
                              nth(nodes, j + 1))) &*&
            node_pred(nth(nodes, len(nodes) - 1),
                      value_of_node(nth(nodes, len(nodes) - 1)),
                      0)))
    )
}

#[lemma]
fn value_of_node(p: *mut Node) -> i32
    requires node_pred(p, _, _)
    ensures true
{
    switch p {
        case 0 => assert(false); // node_pred requires p != 0
        case _ =>
            let Node { next: _, value } = *p;
            value
    }
}

#[lemma]
fn tl_n(l: list<*mut Node>, n: int) -> list<*mut Node>
    requires 0 <= n && n <= len(l)
    ensures len(result) == len(l) - n &&
            (forall<i: int> 0 <= i < len(result) ==> nth(result, i) == nth(l, i + n))
{
    if n == 0 {
        result = l;
    } else {
        result = tl(tl_n(l, n - 1));
    }
}

#[requires(stack != 0 &*& stack_pred(stack, ?nodes))]
#[ensures(result == len(nodes) &*& stack_pred(stack, nodes))]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
        stack != 0 &*& stack_pred(stack, nodes) &*&
        (n != 0 ? node_pred(n, _, ?next_ptr) : true) &*&
        exists<rest: list<*mut Node>>(
            nodes == append(take(i, nodes), cons(n, rest)) &*&
            len(rest) >= 0 &*&
            i + len(rest) == len(nodes)
        )
    )]
    loop {
        if n.is_null() {
            break;
        }
        let old_n = n;
        n = (*n).next;
        i = i + 1;
    }
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}