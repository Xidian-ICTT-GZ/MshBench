#[predicate]
fn node(n: *mut Node, next: *mut Node, value: i32) -> bool {
    (*n).next |-> next &*& (*n).value |-> value
}

#[predicate]
fn stack(s: *mut Stack, nodes: list<*mut Node>) -> bool {
    match nodes {
        cons(h, t) => (*s).head |-> h &*& node(h, match t { cons(h2, _) => h2, nil => std::ptr::null_mut() }, ?v) &*& stack_nodes(t),
        nil => (*s).head |-> std::ptr::null_mut(),
    }
}

#[predicate]
fn stack_nodes(nodes: list<*mut Node>) -> bool {
    match nodes {
        cons(n, ns) => node(n, match ns { cons(n2, _) => n2, nil => std::ptr::null_mut() }, ?v) &*& stack_nodes(ns),
        nil => true,
    }
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    requires stack(stack, ?nodes) &*& stack_nodes(nodes),
    ensures stack(stack, nodes) &*& stack_nodes(nodes) &*& result == length(nodes),
{
    let mut n = (*stack).head;
    let mut i = 0;
    loop
        invariant stack(stack, nodes) &*& stack_nodes(nodes) &*& n == match nodes[i..] { cons(h, _) => h, nil => std::ptr::null_mut() } &*& i <= length(nodes),
    {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}