use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

predicate node(struct Node* n; i32 v, struct Node* next) =
    n->value |-> v &*& n->next |-> next;

predicate nodes(struct Node* n, I32Predicate* p; list<int> vs) =
    switch (vs) {
        case Nil: return n == null_mut();
        case Cons(h, t): return node(n, h, ?next) &*& nodes(next, p, t) &*& p(h) == true;
    };

type I32Predicate = fn(i32) -> bool;

#[requires(n != null_mut() ? nodes(*n, p, ?vs) : vs == Nil)]
#[ensures(vs == ?oldVs && nodes(*n, p, oldVs))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires *n |-> ?node_ptr &*& n != null_mut() &*& p != null_mut();
    //@ ensures *n |-> ?node_ptr_new;
{
    if !(*n).is_null() {
        let node = *n;

        node(node, ?v, ?next) &*& nodes(next, p, ?rest) &*& p(v) == true || p(v) == false;

        bool keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            //@ open nodes(node, p, Cons(v, rest));
            //@ open node(node, v, next);
            filter_nodes(next_ptr, p);
            //@ close node(node, v, next);
            //@ close nodes(node, p, Cons(v, rest));
        } else {
            let next_ = (*node).next;
            //@ open nodes(node, p, Cons(v, rest));
            //@ open node(node, v, next_);
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            //@ close nodes(*n, p, rest);
            return;
        }
        //@ close nodes(*n, p, ?newVs);
    } else {
        //@ assume nodes(null_mut(), p, Nil);
    }
}