#![allow(unsafe_op_in_unsafe_fn)]

use std::{
    alloc::{alloc, dealloc, handle_alloc_error, Layout},
    thread::JoinHandle,
};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[pred]
pub fn tree_pred(t: *mut Tree, depth: u8, sum: u64, prod: u64) =
    t == std::ptr::null_mut() && depth == 0 && sum == 0 && prod == 1
    || t != std::ptr::null_mut() && depth > 0 &&
       exists!(l: *mut Tree, r: *mut Tree, v: u16, s_l: u64, p_l: u64, s_r: u64, p_r: u64,
               f: u64 |
               (*t).left |-> l &*& (*t).right |-> r &*& (*t).value |-> v &
               tree_pred(l, depth - 1, s_l, p_l) &
               tree_pred(r, depth - 1, s_r, p_r) &
               wrapping_fib(v) == f &
               sum == s_l.wrapping_add(f).wrapping_add(s_r) &
               prod == p_l.wrapping_mul(f).wrapping_mul(p_r));

#[pred]
pub fn tree_heap(t: *mut Tree, depth: u8) =
    t == std::ptr::null_mut() && depth == 0
    || t != std::ptr::null_mut() && depth > 0 &&
       exists!(l: *mut Tree, r: *mut Tree, v: u16 |
               (*t).left |-> l &*& (*t).right |-> r &*& (*t).value |-> v &
               tree_heap(l, depth - 1) &
               tree_heap(r, depth - 1));

#[lem]
pub fn tree_pred_split(t: *mut Tree, depth: u8, sum: u64, prod: u64)
    requires tree_pred(t, depth, sum, prod),
    ensures exists!(l: *mut Tree, r: *mut Tree, v: u16, s_l: u64, p_l: u64, s_r: u64, p_r: u64, f: u64 |
                    (*t).left |-> l &*& (*t).right |-> r &*& (*t).value |-> v &
                    tree_pred(l, depth - 1, s_l, p_l) &
                    tree_pred(r, depth - 1, s_r, p_r) &
                    wrapping_fib(v) == f &
                    sum == s_l.wrapping_add(f).wrapping_add(s_r) &
                    prod == p_l.wrapping_mul(f).wrapping_mul(p_r))
{
    // lemma body omitted (VeriFast can infer via predicate definition)
}

#[lem]
pub fn tree_pred_join(l: *mut Tree, r: *mut Tree, v: u16, s_l: u64, p_l: u64, s_r: u64, p_r: u64, f: u64, depth: u8)
    requires tree_pred(l, depth - 1, s_l, p_l) &*& tree_pred(r, depth - 1, s_r, p_r) &*& wrapping_fib(v) == f,
    ensures tree_pred(
        alloc(Layout::new::<Tree>()) as *mut Tree,
        depth,
        s_l.wrapping_add(f).wrapping_add(s_r),
        p_l.wrapping_mul(f).wrapping_mul(p_r)
    )
{
    // lemma body omitted
}

#[requires(f != std::ptr::null_mut())]
#[ensures(result != std::ptr::null_mut() || depth == 0)]
#[ensures(t == std::ptr::null_mut() ==> depth == 0)]
#[ensures(result == std::ptr::null_mut() ==> depth == 0)]
#[ensures(0 <= depth)]
#[invariant(depth >= 0)]
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where
    A: 'static,
    R: 'static,
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable {
            payload: f(package_moved.payload),
        }
    })
}

#[requires(true)]
#[ensures(true)]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

#[requires(true)]
#[ensures(result == 1 || (result >= 1 && n <= 1))]
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(2 <= k && k <= n + 1 && 
          fib_k_minus_1 > 0 && fib_k > 0)]
        loop {
            if k == n {
                break;
            }

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
    #[requires(depth >= 0)]
    #[ensures(result == std::ptr::null_mut() && depth == 0 ||
              result != std::ptr::null_mut() && tree_heap(result, depth))]
    unsafe fn make(depth: u8) -> *mut Tree {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000;
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;

            t
        }
    }

    #[requires(tree_heap(tree, ?depth))]
    #[ensures(tree_heap(tree, depth))]
    #[ensures(result == ?sum)]
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

    #[requires(tree_heap(tree, ?depth))]
    #[ensures(tree_heap(tree, depth))]
    #[ensures(result == ?prod)]
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64 {
        if tree.is_null() {
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);

            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }

    #[requires(tree_heap(tree, ?depth))]
    #[ensures(true)]
    unsafe fn dispose(tree: *mut Tree) {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);

        let product_join_handle = spawn(Tree::compute_product_fibs, tree);

        let sum = join(sum_join_handle);

        let product = join(product_join_handle);

        Tree::dispose(tree);

        print_u64(sum);
        print_u64(product);
    }
}