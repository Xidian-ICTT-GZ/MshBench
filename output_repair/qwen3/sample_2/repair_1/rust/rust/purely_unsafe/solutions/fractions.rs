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

predicate sendable<T>(Sendable<T> s; T t) = s.payload |-> t;

#[requires(tree(tree_ptr, depth))]
#[ensures(match result {
    std::ptr::null_mut() => depth == 0,
    _ => tree(result, depth)
})]
unsafe fn make(depth: u8, tree_ptr: *mut Tree) -> *mut Tree {
    if depth == 0 {
        std::ptr::null_mut()
    } else {
        let left = Self::make(depth - 1, std::ptr::null_mut());
        let right = Self::make(depth - 1, std::ptr::null_mut());
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

impl Tree {
    #[requires(depth <= 255)]
    #[ensures(match result {
        std::ptr::null_mut() => depth == 0,
        _ => tree(result, depth)
    })]
    unsafe fn make(depth: u8) -> *mut Tree {
        Self::make(depth, std::ptr::null_mut())
    }

    #[requires(tree(tree, ?d))]
    #[ensures(tree(tree, d) &*& result == _)]
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
    #[ensures(tree(tree, d) &*& result == _)]
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

#[requires(sendable(?s, ?a))]
#[ensures(sendable(?s2, ?r) &*& r == f(a))]
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

#[requires(sendable(?s, ?r))]
#[ensures(r == result)]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
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