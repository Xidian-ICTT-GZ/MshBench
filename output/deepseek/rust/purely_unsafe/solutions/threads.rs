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
            tree_full(left) && tree_full(right)
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
            tree_fraction(left, p) && tree_fraction(right, p)
        )
    }
}

#[predicate]
fn sendable_points_to<T>(s: *mut Sendable<T>, payload: T) -> bool {
    unsafe { (*s).payload == payload }
}

#[predicate]
fn join_handle_points_to<R>(h: *mut JoinHandle<Sendable<R>>, t: *mut Tree, p: Perm) -> bool {
    exists!(s: *mut Sendable<R> |
        sendable_points_to(s, Tree::compute_sum_fibs(t)) &&
        tree_fraction(t, p)
    )
}

#[requires(tree_full(tree))]
#[ensures(tree_full(result))]
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

#[requires(join_handle_points_to(&h, tree, 1/2))]
#[ensures(tree_full(tree))]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

#[requires(n <= 5000)]
#[ensures(result <= 18446744073709551615u64)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_k_minus_1 <= 18446744073709551615u64)]
        #[invariant(fib_k <= 18446744073709551615u64)]
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
    #[ensures(result.is_null() || tree_full(result))]
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

    #[requires(tree_full(tree))]
    #[ensures(tree_full(tree))]
    #[ensures(result <= 18446744073709551615u64)]
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

#[requires(value <= 18446744073709551615u64)]
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        let left = (*tree).left;
        let right = (*tree).right;

        let left_join_handle = spawn(Tree::compute_sum_fibs, left);

        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);

        let right_sum = join(right_join_handle);

        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);

        print_u64(sum)
    }
}