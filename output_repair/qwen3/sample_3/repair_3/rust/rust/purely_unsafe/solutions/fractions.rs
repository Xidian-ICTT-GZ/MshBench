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

predicate TreeNode(ptr: *mut Tree; v: u16, l: *mut Tree, r: *mut Tree) =
    ptr != null() &*&
    (*ptr).left |-> l &*&
    (*ptr).right |-> r &*&
    (*ptr).value |-> v;

predicate tree(ptr: *mut Tree) =
    ptr == null()
    ||
    exists(v: u16, l: *mut Tree, r: *mut Tree;
        TreeNode(ptr, v, l, r) &*& tree(l) &*& tree(r));

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

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
requires true
ensures true
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
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
    unsafe fn make(depth: u8) -> *mut Tree
    requires true
    ensures tree(result)
    {
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

    unsafe fn compute_sum_fibs(tree_ptr: *mut Tree) -> u64
    requires tree(tree_ptr)
    ensures tree(tree_ptr)
    {
        if tree_ptr.is_null() {
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree_ptr).left);
            let f = wrapping_fib((*tree_ptr).value);
            let right_sum = Self::compute_sum_fibs((*tree_ptr).right);

            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

    unsafe fn compute_product_fibs(tree_ptr: *mut Tree) -> u64
    requires tree(tree_ptr)
    ensures tree(tree_ptr)
    {
        if tree_ptr.is_null() {
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree_ptr).left);
            let f = wrapping_fib((*tree_ptr).value);
            let right_product = Self::compute_product_fibs((*tree_ptr).right);

            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
}

unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree_ptr = Tree::make(22);

        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree_ptr);

        let product_join_handle = spawn(Tree::compute_product_fibs, tree_ptr);

        let sum = join(sum_join_handle);

        let product = join(product_join_handle);

        print_u64(sum);
        print_u64(product);
    }
}