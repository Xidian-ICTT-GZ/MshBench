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
predicate tree(t: *mut Tree; depth: u8) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        depth > 0 &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?v &*&
        std::alloc::alloc_block(t as *mut u8, std::mem::size_of::<Tree>()) &*&
        tree(left, depth - 1) &*&
        tree(right, depth - 1)
    };

predicate tree_shared(t: *mut Tree; depth: u8, frac: real) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        depth > 0 &*&
        [frac](*t).left |-> ?left &*&
        [frac](*t).right |-> ?right &*&
        [frac](*t).value |-> ?v &*&
        tree_shared(left, depth - 1, frac) &*&
        tree_shared(right, depth - 1, frac)
    };

predicate alloc_block(ptr: *mut u8, size: usize) =
    ptr |-> _ &*& chars(ptr, size, _);

lemma void tree_dealloc(struct Tree* t, uint8_t depth)
    requires tree(t, depth);
    ensures true;
{
    open tree(t, depth);
    if (t != null) {
        tree_dealloc((*t).left, depth - 1);
        tree_dealloc((*t).right, depth - 1);
        close tree(t, depth);
    }
}
@*/

#[requires(true)]
#[ensures(tree(result, depth))]
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
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop
        /*@
        invariant
            2 <= k && k <= n + 1 &*&
            fib_k_minus_1 |-> ?fkm1 &*&
            fib_k |-> ?fk &*&
            k |-> ?kv &*&
            kv == k;
        @*/
        {
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
    #[ensures(tree(result, depth))]
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

    #[requires(tree_shared(tree, ?depth, 1.0/2.0))]
    #[ensures(tree_shared(tree, depth, 1.0/2.0))]
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

    #[requires(tree_shared(tree, ?depth, 1.0/2.0))]
    #[ensures(tree_shared(tree, depth, 1.0/2.0))]
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

    #[requires(tree(tree, ?depth))]
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