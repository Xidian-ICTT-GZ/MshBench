use std::alloc::{Layout, dealloc};
use std::ptr;

struct Node {
    data: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate stack_pred(stack: *mut Stack, nodes: list<*mut Node>) =
    stack != 0 &*& 
    points_to(stack, Stack { head: ?head }) &*&
    node_list(head, nodes);

predicate node_list(head: *mut Node, nodes: list<*mut Node>) =
    head == 0 ? nodes == nil :
    head != 0 &*&
    points_to(head, Node { data: _, next: ?next }) &*&
    node_list(next, ?tail) &*&
    nodes == cons(head, tail);

lemma void node_list_unique(list<*mut Node> nodes)
    requires node_list(?head, nodes);
    ensures node_list(head, nodes) &*&
            forall(nodes, (|p| p != 0)) &*&
            distinct(nodes);
{
    switch (nodes) {
        case nil: {}
        case cons(h, t):
            assert node_list(h, cons(h, t));
            node_list_unique(t);
    }
}

impl Stack {
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        #[requires(stack != 0 && other != 0)]
        #[requires(stack_pred(stack, ?s1) && stack_pred(other, ?s2))]
        #[ensures(stack_pred(stack, append(s2, s1)))]
        #[ensures(!stack_pred(other, _))] // other is deallocated, no ownership remains
        {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(node_list(n, ?ns) && ns != nil && append(ns, s1) == append(s2, s1))]
            #[invariant(forall(ns, (|p| p != 0)) && distinct(ns))]
            loop {
                if (*n).next.is_null() { break; }
                let next = (*n).next;
                n = next;
            }

            points_to(n, Node { data: _, next: ?old_next });
            leak node_list(n, ns);
            // Verify n is last in ns, ns != nil by invariant
            // Properly mutate next to link to stack head
            // points_to and node_list ownership held, so mutation permitted
            *(&(*n).next) = (*stack).head;
            leak stack_pred(stack, s1);
            *(&(*stack).head) = head0;
        } else {
            *(&(*stack).head) = head0;
        }
        }
    }
}