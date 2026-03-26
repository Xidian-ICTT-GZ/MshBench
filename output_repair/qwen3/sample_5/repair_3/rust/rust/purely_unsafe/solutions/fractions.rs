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

predicate Tree_tree(*mut Tree t; u8 depth) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?v &*&
        v == 5000 &*&
        Tree_tree(left, if depth == 0 { 0 } else { depth - 1 }) &*&
        Tree_tree(right, if depth == 0 { 0 } else { depth - 1 }) &*&
        depth > 0
    };

#[requires(depth <= 22)]
#[ensures(match result { std::ptr::null_mut() => depth == 0, _ => Tree_tree(result, depth) })]
unsafe fn Tree_make(depth: u8) -> *mut Tree {
    if depth == 0 {
        std::ptr::null_mut()
    } else {
        let left = Tree_make(depth - 1);
        let right = Tree_make(depth - 1);
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

#[requires(Tree_tree(tree_ptr, ?d))]
#[ensures(Tree_tree(tree_ptr, d))]
unsafe fn Tree_compute_sum_fibs(tree_ptr: *mut Tree) -> u64 {
    if tree_ptr.is_null() {
        0
    } else {
        let left_sum = Tree_compute_sum_fibs((*tree_ptr).left);
        let f = wrapping_fib((*tree_ptr).value);
        let right_sum = Tree_compute_sum_fibs((*tree_ptr).right);

        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

#[requires(Tree_tree(tree_ptr, ?d))]
#[ensures(Tree_tree(tree_ptr, d))]
unsafe fn Tree_compute_product_fibs(tree_ptr: *mut Tree) -> u64 {
    if tree_ptr.is_null() {
        1
    } else {
        let left_product = Tree_compute_product_fibs((*tree_ptr).left);
        let f = wrapping_fib((*tree_ptr).value);
        let right_product = Tree_compute_product_fibs((*tree_ptr).right);

        left_product.wrapping_mul(f).wrapping_mul(right_product)
    }
}

#[requires(n <= 5000)]
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n + 1 && fib_k_minus_1 >= 1 && fib_k >= 1)]
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

#[requires(true)]
#[ensures(true)]
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

#[requires(true)]
#[ensures(true)]
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

fn main() {
    unsafe {
        let tree = Tree_make(22);

        let sum_join_handle = spawn(Tree_compute_sum_fibs, tree);

        let product_join_handle = spawn(Tree_compute_product_fibs, tree);

        let sum = join(sum_join_handle);

        let product = join(product_join_handle);

        print_u64(sum);
        print_u64(product);
    }
}