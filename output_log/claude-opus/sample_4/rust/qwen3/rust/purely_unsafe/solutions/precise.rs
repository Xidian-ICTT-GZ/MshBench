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

/*@
fix wrapping_fib_pure(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        wrapping_fib_pure((n - 1) as u16).wrapping_add(wrapping_fib_pure((n - 2) as u16))
    }
}

pred tree_heap(t: *mut Tree, depth: u8) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        depth > 0 &*&
        (*t).left |-> ?l &*& (*t).right |-> ?r &*& (*t).value |-> ?v &*&
        tree_heap(l, (depth - 1) as u8) &*&
        tree_heap(r, (depth - 1) as u8)
    };

pred tree_heap_half(t: *mut Tree, depth: u8; frac f) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        depth > 0 &*&
        [f](*t).left |-> ?l &*& [f](*t).right |-> ?r &*& [f](*t).value |-> ?v &*&
        tree_heap_half(l, (depth - 1) as u8; f) &*&
        tree_heap_half(r, (depth - 1) as u8; f)
    };

lem tree_heap_split(t: *mut Tree, depth: u8)
    req tree_heap(t, depth);
    ens tree_heap_half(t, depth; 1/2) &*& tree_heap_half(t, depth; 1/2);
{
    if t == std::ptr::null_mut() {
    } else {
        open tree_heap(t, depth);
        tree_heap_split((*t).left, (depth - 1) as u8);
        tree_heap_split((*t).right, (depth - 1) as u8);
        close tree_heap_half(t, depth; 1/2);
        close tree_heap_half(t, depth; 1/2);
    }
}

lem tree_heap_merge(t: *mut Tree, depth: u8)
    req tree_heap_half(t, depth; 1/2) &*& tree_heap_half(t, depth; 1/2);
    ens tree_heap(t, depth);
{
    if t == std::ptr::null_mut() {
        open tree_heap_half(t, depth; 1/2);
        open tree_heap_half(t, depth; 1/2);
        close tree_heap(t, depth);
    } else {
        open tree_heap_half(t, depth; 1/2);
        open tree_heap_half(t, depth; 1/2);
        tree_heap_merge((*t).left, (depth - 1) as u8);
        tree_heap_merge((*t).right, (depth - 1) as u8);
        close tree_heap(t, depth);
    }
}

pred_ctor sum_pre(tree: *mut Tree, depth: u8)() = tree_heap_half(tree, depth; 1/2);
pred_ctor sum_post(tree: *mut Tree, depth: u8)(result: u64) = tree_heap_half(tree, depth; 1/2);

pred_ctor prod_pre(tree: *mut Tree, depth: u8)() = tree_heap_half(tree, depth; 1/2);
pred_ctor prod_post(tree: *mut Tree, depth: u8)(result: u64) = tree_heap_half(tree, depth; 1/2);

pred thread_run_pre_sum(data: *mut Tree, depth: u8) = tree_heap_half(data, depth; 1/2);
pred thread_run_post_sum(data: *mut Tree, depth: u8, result: u64) = tree_heap_half(data, depth; 1/2);

pred thread_run_pre_prod(data: *mut Tree, depth: u8) = tree_heap_half(data, depth; 1/2);
pred thread_run_post_prod(data: *mut Tree, depth: u8, result: u64) = tree_heap_half(data, depth; 1/2);
@*/

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

#[requires(true)]
#[ensures(result == wrapping_fib_pure(n))]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n && fib_k_minus_1 == wrapping_fib_pure((k - 1) as u16) && fib_k == wrapping_fib_pure(k))]
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
    #[requires(true)]
    #[ensures(tree_heap(result, depth))]
    unsafe fn make(depth: u8) -> *mut Tree {
        if depth == 0 {
            //@ close tree_heap(std::ptr::null_mut(), 0u8);
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
            //@ close tree_heap(t, depth);
            t
        }
    }

    #[requires(tree_heap_half(tree, depth; 1/2))]
    #[ensures(tree_heap_half(tree, depth; 1/2))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        //@ open tree_heap_half(tree, depth; 1/2);
        if tree.is_null() {
            //@ close tree_heap_half(tree, depth; 1/2);
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree_heap_half(tree, depth; 1/2);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

    #[requires(tree_heap_half(tree, depth; 1/2))]
    #[ensures(tree_heap_half(tree, depth; 1/2))]
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64 {
        //@ open tree_heap_half(tree, depth; 1/2);
        if tree.is_null() {
            //@ close tree_heap_half(tree, depth; 1/2);
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close tree_heap_half(tree, depth; 1/2);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }

    #[requires(tree_heap(tree, depth))]
    #[ensures(true)]
    unsafe fn dispose(tree: *mut Tree) {
        //@ open tree_heap(tree, depth);
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

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let tree = Tree::make(22);
        //@ tree_heap_split(tree, 22u8);

        let sum = Tree::compute_sum_fibs(tree);

        let product = Tree::compute_product_fibs(tree);

        //@ tree_heap_merge(tree, 22u8);
        Tree::dispose(tree);

        print_u64(sum);
        print_u64(product);
    }
}