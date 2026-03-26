#![allow(unsafe_op_in_unsafe_fn)]

use std::{
    alloc::{alloc, handle_alloc_error, Layout},
    thread::JoinHandle,
};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn sendable<T>(s: &Sendable<T>) -> bool { true }

#[predicate]
fn sendable_owned<T>(s: Sendable<T>) -> bool { true }

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: u16) -> bool {
    unsafe { (*t).left == left && (*t).right == right && (*t).value == value }
}

#[predicate]
fn tree_full(t: *mut Tree) -> bool {
    if t.is_null() {
        true
    } else {
        exists!(left: *mut Tree, right: *mut Tree, value: u16 |
            tree_points_to(t, left, right, value) &&
            tree_full(left) &&
            tree_full(right)
        )
    }
}

#[predicate]
fn tree_fraction(t: *mut Tree, p: Perm) -> bool {
    if t.is_null() {
        true
    } else {
        exists!(left: *mut Tree, right: *mut Tree, value: u16 |
            tree_points_to(t, left, right, value) @ p &&
            tree_fraction(left, p) &&
            tree_fraction(right, p)
        )
    }
}

#[lemma]
#[requires(tree_full(t))]
#[ensures(tree_fraction(t, 1/2))]
fn split_tree_fraction(t: *mut Tree) { }

#[lemma]
#[requires(tree_fraction(t, p1))]
#[requires(tree_fraction(t, p2))]
#[ensures(tree_fraction(t, p1 + p2))]
fn merge_tree_fraction(t: *mut Tree, p1: Perm, p2: Perm) { }

#[lemma]
#[requires(tree_fraction(t, 1))]
#[ensures(tree_full(t))]
fn tree_fraction_to_full(t: *mut Tree) { }

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where
    A: 'static,
    R: 'static,
{
    #[requires(sendable_owned(package))]
    #[ensures(sendable_owned(result))]
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable {
            payload: f(package_moved.payload),
        }
    })
}

#[requires(sendable_owned(h))]
#[ensures(sendable_owned(result))]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

#[requires(n <= 65535)]
#[ensures(result <= 18446744073709551615)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_k_minus_1 <= 18446744073709551615)]
        #[invariant(fib_k <= 18446744073709551615)]
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
    #[requires(depth <= 255)]
    #[ensures(tree_full(result))]
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

    #[requires(tree_fraction(tree, 1/2))]
    #[ensures(tree_fraction(tree, 1/2))]
    #[ensures(result <= 18446744073709551615)]
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

    #[requires(tree_fraction(tree, 1/2))]
    #[ensures(tree_fraction(tree, 1/2))]
    #[ensures(result <= 18446744073709551615)]
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
}

#[requires(value <= 18446744073709551615)]
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        
        split_tree_fraction(tree);
        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);

        let product_join_handle = spawn(Tree::compute_product_fibs, tree);

        let sum = join(sum_join_handle);

        let product = join(product_join_handle);

        print_u64(sum);
        print_u64(product);
    }
}