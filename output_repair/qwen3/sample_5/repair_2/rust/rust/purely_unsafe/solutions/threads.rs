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

predicate Tree(t: *mut Tree; depth: nat) =
    t == std::ptr::null_mut() ?
        depth == 0
    :
        (t as usize) % std::mem::align_of::<Tree>() == 0 &&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        [(*t).value] &*&
        Tree(left, ?d1) &*&
        Tree(right, ?d2) &*&
        depth == 1 + max(d1, d2);

predicate SendableOwned<T>(s: *const Sendable<T>) =
    (s as usize) % std::mem::align_of::<Sendable<T>>() == 0 &&
    [(*s).payload];

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

#[requires(n <= 93)]
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            #[invariant(k >= 2 && k <= n && fib_k_minus_1 >= 1 && fib_k >= 1)]
            {
                if k == n {
                    break;
                }

                let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);

                k += 1;
                fib_k_minus_1 = fib_k;
                fib_k = fib_k_plus_1;
            }
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
    #[ensures(Tree(result, depth))]
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
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    #[requires(Tree(tree, ?d))]
    #[ensures(true)]
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

#[requires(true)]
#[ensures(true)]
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