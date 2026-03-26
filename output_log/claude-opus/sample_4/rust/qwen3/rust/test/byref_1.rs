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
pub struct node_pred(*mut Node, i32, *mut Node) = 
    self.0 != null_mut() &*&
    malloc_block_Node(self.0) &*&
    (*self.0).value |-> self.1 &*&
    (*self.0).next |-> self.2;

#[lemma]
#[requires(node_pred(p, v, q))]
#[ensures(node_pred(p, v, q))]
pub fn node_pred_preserves(p: *mut Node, v: i32, q: *mut Node) {}

#[pred]
pub struct list_pred(*mut Node, *mut Node);

#[pred]
pub struct list_pred(h: *mut Node, t: *mut Node) = 
    h == t ?
        emp
    :
        node_pred(h, _, ?next) &*& list_pred(next, t);

#[lemma]
#[requires(list_pred(h, t))]
#[ensures(list_pred(h, t))]
pub fn list_pred_preserves(h: *mut Node, t: *mut Node) {}

#[lemma]
#[requires(list_seg::<Node>(h, m, t))]
#[ensures(list_seg::<Node>(h, m, t))]
pub fn list_seg_preserves<T>(h: *mut T, m: *mut T, t: *mut T) {}

#[predicate]
pub fn node_own(p: *mut Node) = p != null_mut() &*& node_pred(p, _, _);

#[predicate]
pub fn list_own(h: *mut Node) = h == null_mut() ?
    emp
:
    list_pred(h, null_mut());

#[predicate]
pub fn list_seg_own(h: *mut Node, t: *mut Node) = 
    h == t ?
        emp
    :
        node_pred(h, _, ?next) &*& list_seg_own(next, t);

#[requires(node_own(*n))]
#[requires(p is fn(i32) -> bool)]
#[ensures(list_own(*n))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    #[invariant(list_own(*n))]
{
    if !(*n).is_null() {
        let node = *n;
        #[ghost] let old_node = node;
        #[ghost] let old_next = (*node).next;
        
        // We own node and its next pointer by node_pred
        #[open node_pred(node, _, _);]
        
        let keep = p((*node).value);
        if keep {
            let next_ptr = &mut (*node).next;
            // node_pred(node, value, next) holds, owning next pointer
            filter_nodes(next_ptr, p);
            #[close node_pred(node, (*node).value, (*node).next);]
        } else {
            let next_ = (*node).next;
            // We own node, so we can deallocate it
            #[close node_pred(node, (*node).value, next_);]
            dealloc(node as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}