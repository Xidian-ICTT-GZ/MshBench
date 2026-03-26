use std::alloc::{dealloc, Layout};
use std::ptr::null_mut;

struct Node {
    value: i32,
    next: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[pred]
pub struct list_seg<T>(*mut T, *mut T, *mut T);

#[pred]
pub struct node_pred(*mut Node, i32, *mut Node);

#[lemma]
#[requires(node_pred(p, v, q))]
#[ensures(node_pred(p, v, q))]
pub fn node_pred_preserves(p: *mut Node, v: i32, q: *mut Node) {}

#[pred]
pub struct list_pred(*mut Node, *mut Node);

#[lemma]
#[requires(list_pred(h, t))]
#[ensures(list_pred(h, t))]
pub fn list_pred_preserves(h: *mut Node, t: *mut Node) {}

#[lemma]
#[requires(list_seg::<Node>(h, m, t))]
#[ensures(list_seg::<Node>(h, m, t))]
pub fn list_seg_preserves<T>(h: *mut T, m: *mut T, t: *mut T) {}

#[predicate]
pub fn node_own(p: *mut Node) = 
    p != null_mut() 
    &*& node_pred(p, _, _);

#[predicate]
pub fn list_own(h: *mut Node) = 
    (h == null_mut()) 
    || list_pred(h, null_mut());

#[predicate]
pub fn list_seg_own(h: *mut Node, t: *mut Node) = 
    (h == t) 
    || (h != null_mut() &*& node_pred(h, _, _) &*& list_seg_own((*h).next, t));

#[requires(node_own(*n))]
#[requires(true)]  // p is a predicate function, no heap resources to own
#[ensures(node_own(*n) || *n == null_mut())]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    #[invariant(n != null_mut() &*& (node_own(*n) || *n == null_mut()))]
{
    if !(*n).is_null() {
        let node = *n;
        #[ghost] let old_node = node;
        #[ghost] let old_next = (*node).next;

        #[assert] node_pred(node, (*node).value, (*node).next);

        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            #[assert] node_pred(node, (*node).value, (*next_ptr));
            // Call recursively owning the next node
            filter_nodes(next_ptr, p);
        } else {
            let next_ = (*node).next;
            #[assert] node_pred(node, (*node).value, next_);
            // Free the node, releasing ownership
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            // Now *n points to next_, own the remainder list
            filter_nodes(n, p);
        }
    }
}