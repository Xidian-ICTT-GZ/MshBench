#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

#[predicate]
fn tree_pred(ptr: *mut Tree, depth: u8, value: u16, left: *mut Tree, right: *mut Tree) =
    ptr |-> Tree { left: left, right: right, value: value } &*&
    if depth == 0 {
        left == std::ptr::null_mut() &*& right == std::ptr::null_mut()
    } else {
        true
    };

#[predicate]
fn TreePred<'a>(ptr: *mut Tree, depth: u8, left_pred_opt: Option<&'a TreePred<'a>>, right_pred_opt: Option<&'a TreePred<'a>>, value: u16) =
    ptr |-> Tree { left: ?left_ptr, right: ?right_ptr, value: value } &*&
    (depth == 0 ?
        left_ptr == std::ptr::null_mut() &*& right_ptr == std::ptr::null_mut() &*&
        left_pred_opt == None &*& right_pred_opt == None
        :
        left_pred_opt == Some(?left_pred) &*& left_pred.ptr == left_ptr &*& left_pred.depth == depth - 1 &*&
        right_pred_opt == Some(?right_pred) &*& right_pred.ptr == right_ptr &*& right_pred.depth == depth - 1
    ) &*&
    exist<'a>(|l: TreePred<'a>, r: TreePred<'a>| {
        // Recursively owns left and right subtrees
        match (left_pred_opt, right_pred_opt) {
            (Some(lp), Some(rp)) => l.ptr == lp.ptr &*& r.ptr == rp.ptr &*&
                                   True,
            _ => true
        }
    });

#[lemma]
fn tree_pred_split(ptr: *mut Tree, depth: u8, value: u16, left: *mut Tree, right: *mut Tree)
    requires
        ptr |-> Tree { left: left, right: right, value: value } &*&
        TreePred(ptr, depth, _, _, value),
    ensures
        TreePred(ptr, depth, Some(?l), Some(?r), value) &*&
        l.ptr == left &*& r.ptr == right &*&
        l.depth == depth - 1 &*& r.depth == depth - 1,
{
    open TreePred(ptr, depth, _, _, value);
    close TreePred(ptr, depth, Some(l), Some(r), value);
}

#[lemma]
fn tree_pred_base(ptr: *mut Tree, value: u16)
    requires
        ptr |-> Tree { left: std::ptr::null_mut(), right: std::ptr::null_mut(), value: value } &*&
        TreePred(ptr, 0, None, None, value),
    ensures
        TreePred(ptr, 0, None, None, value),
{
    open TreePred(ptr, 0, None, None, value);
    close TreePred(ptr, 0, None, None, value);
}

#[predicate]
fn tree_root(ptr: *mut Tree, depth: u8) =
    if depth == 0 {
        ptr == std::ptr::null_mut()
    } else {
        exists l: *mut Tree, r: *mut Tree, value: u16, left_pred: TreePred, right_pred: TreePred:
            TreePred(ptr, depth, Some(&left_pred), Some(&right_pred), value) &*&
            tree_root(l, depth - 1) &*&
            tree_root(r, depth - 1) &*&
            left_pred.ptr == l &*& right_pred.ptr == r
    };

#[requires(n <= 1 ==> n == 0)]
#[ensures(result == 1)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n &&
            fib_k == wrapping_fib(k) && fib_k_minus_1 == wrapping_fib(k - 1))]
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

    #[requires(depth <= 22)]
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
            // After allocation, owns t |-> uninitialized Tree
            #[ghost]
            {
                // close TreePred predicate after initialization
                assume(t |-> Tree {left: std::ptr::null_mut(), right: std::ptr::null_mut(), value: 0});
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            // Close predicate describing ownership of this tree node
            close TreePred(t, depth, 
                if depth == 0 { None } else { Some(&TreePred(left, depth - 1, None, None, value)) },
                if depth == 0 { None } else { Some(&TreePred(right, depth - 1, None, None, value)) },
                value);
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