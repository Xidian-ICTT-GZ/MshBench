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

predicate tree(*mut Tree t; u8 depth) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?v &*&
        v == 5000 &*&
        tree(left, if depth == 0 { 0 } else { depth - 1 }) &*&
        tree(right, if depth == 0 { 0 } else { depth - 1 }) &*&
        depth > 0
    };

#[requires(depth <= 255)]
#[ensures(match result { None => depth == 0, Some(t) => tree(t, depth) })]
unsafe fn make_impl(depth: u8) -> Option<*mut Tree> {
    if depth == 0 {
        None
    } else {
        let left_opt = make_impl(depth - 1);
        let right_opt = make_impl(depth - 1);
        let value = 5000;
        let layout = Layout::new::<Tree>();
        let t = alloc(layout) as *mut Tree;
        if t.is_null() {
            handle_alloc_error(layout);
        }
        let left = match left_opt {
            None => std::ptr::null_mut(),
            Some(p) => p,
        };
        let right = match right_opt {
            None => std::ptr::null_mut(),
            Some(p) => p,
        };
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        Some(t)
    }
}

#[requires(tree(arg, ?d))]
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

#[requires(n <= 1 || n >= 2)]
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            #[invariant(k >= 2 && k <= n)]
            #[invariant(fib_k_minus_1 >= 1 && fib_k >= 1)]
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
    #[requires(depth <= 22)]
    #[ensures(match result { std::ptr::null_mut() => depth == 0, _ => tree(result, depth) })]
    unsafe fn make(depth: u8) -> *mut Tree {
        match make_impl(depth) {
            None => std::ptr::null_mut(),
            Some(t) => t,
        }
    }

    #[requires(tree(tree, ?d))]
    #[ensures(tree(tree, d))]
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

    #[requires(tree(tree, ?d))]
    #[ensures(tree(tree, d))]
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

        print_u64(sum);
        print_u64(product);
    }
}