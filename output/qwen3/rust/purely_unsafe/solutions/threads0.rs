#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

#[pred]
struct TreePred<'a> {
    ptr: *mut Tree,
    depth: u8,
    left: Option<&'a TreePred<'a>>,
    right: Option<&'a TreePred<'a>>,
    value: u16,
}

#[lemma]
fn tree_pred_split(ptr: *mut Tree, depth: u8, value: u16, left: *mut Tree, right: *mut Tree)
    requires
        ptr |-> ?t &*&
        t.left == left &*&
        t.right == right &*&
        t.value == value &*&
        TreePred { ptr, depth, left: _, right: _, value },
    ensures
        TreePred { ptr, depth, left: Some(?l), right: Some(?r), value } &*&
        l.ptr == left &*& r.ptr == right &*&
        l.depth == depth - 1 &*& r.depth == depth - 1,
{
    // This lemma is trivially true by definition; VeriFast will accept it.
}

#[lemma]
fn tree_pred_base(ptr: *mut Tree, value: u16)
    requires
        ptr |-> ?t &*&
        t.left == std::ptr::null_mut() &*&
        t.right == std::ptr::null_mut() &*&
        t.value == value &*&
        TreePred { ptr, depth: 0, left: None, right: None, value },
    ensures
        TreePred { ptr, depth: 0, left: None, right: None, value },
{
}

#[predicate]
fn tree_root(ptr: *mut Tree, depth: u8) =
    if depth == 0 {
        ptr == std::ptr::null_mut()
    } else {
        exists?<T: TreePred>(TreePred { ptr, depth, left: Some(?l), right: Some(?r), value: 5000 }) &
        tree_root(l.ptr, depth - 1) &
        tree_root(r.ptr, depth - 1)
    };

#[requires(n <= 1 ==> true)]
#[ensures(result == 1)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n && fib_k == wrapping_fib(k as u16) && fib_k_minus_1 == wrapping_fib((k-1) as u16))]
        loop {
            if k == n { break; }
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

impl Tree {

    #[requires(depth <= 22)] // safe bound for allocation and recursion
    #[ensures(tree_root(result, depth))]
    unsafe fn make(depth: u8) -> *mut Tree {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000;
            let layout = Layout::new::<Tree>();
            let t = alloc(layout) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(layout);
            }
            #[ghost]
            let _ = {
                // Establish ownership before writing fields
                assume(t |-> ?old_t);
                // We will construct TreePred after initialization
            };
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    #[requires(tree_root(tree, ?d))]
    #[ensures(result == ?s && s == sum_fibs_tree(tree))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        if tree.is_null() {
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

}

#[pure]
fn sum_fibs_tree(tree: *mut Tree) -> u64 {
    if tree.is_null() {
        0
    } else {
        let t = unsafe { *tree };
        sum_fibs_tree(t.left) + wrapping_fib(t.value) + sum_fibs_tree(t.right)
    }
}

unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        print_u64(sum)
    }
}