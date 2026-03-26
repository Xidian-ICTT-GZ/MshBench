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

/*@

pred Tree_own(t: *mut Tree; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        depth > 0 &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        struct_Tree_padding(t) &*&
        Tree_own(left, depth - 1) &*&
        Tree_own(right, depth - 1)
    };

pred Tree_frac(t: *mut Tree, f: real; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        depth > 0 &*&
        [f](*t).left |-> ?left &*&
        [f](*t).right |-> ?right &*&
        [f](*t).value |-> ?value &*&
        [f]struct_Tree_padding(t) &*&
        Tree_frac(left, f, depth - 1) &*&
        Tree_frac(right, f, depth - 1)
    };

lem Tree_split(t: *mut Tree)
    req Tree_own(t, ?depth);
    ens Tree_frac(t, 1/2, depth) &*& Tree_frac(t, 1/2, depth);
{
    open Tree_own(t, depth);
    if t == 0 {
        close Tree_frac(t, 1/2, depth);
        close Tree_frac(t, 1/2, depth);
    } else {
        Tree_split((*t).left);
        Tree_split((*t).right);
        close Tree_frac(t, 1/2, depth);close Tree_frac(t, 1/2, depth);
    }
}

lem Tree_merge(t: *mut Tree)
    req Tree_frac(t, 1/2, ?depth) &*& Tree_frac(t, 1/2, depth);
    ens Tree_own(t, depth);
{
    open Tree_frac(t, 1/2, depth);
    open Tree_frac(t, 1/2, depth);
    if t == 0 {
        close Tree_own(t, depth);
    } else {
        Tree_merge((*t).left);
        Tree_merge((*t).right);
        close Tree_own(t, depth);
    }
}

pred thread_run_pre(f: *Spawnee<*mut Tree, u64>, data: *mut Tree, frac: real) =
    Tree_frac(data, frac, _);

pred thread_run_post(f: *Spawnee<*mut Tree, u64>, data: *mut Tree, frac: real) =
    Tree_frac(data, frac, _);

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

unsafe fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens true;
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop
        //@ inv k >= 2 &*& k <= n;
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
    unsafe fn make(depth: u8) -> *mut Tree
    //@ req true;
    //@ ens Tree_own(result, depth as i32);
    {
        if depth == 0 {
            //@ close Tree_own(std::ptr::null_mut(), 0);
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
            //@ close Tree_own(t, depth as i32);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree_frac(tree, ?f, ?depth);
    //@ ens Tree_frac(tree, f, depth);
    {
        //@ open Tree_frac(tree, f, depth);
        if tree.is_null() {
            //@ close Tree_frac(tree, f, depth);
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f_val = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close Tree_frac(tree, f, depth);
            left_sum.wrapping_add(f_val).wrapping_add(right_sum)
        }
    }

    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req Tree_frac(tree, ?f, ?depth);
    //@ ens Tree_frac(tree, f, depth);
    {
        //@ open Tree_frac(tree, f, depth);
        if tree.is_null() {
            //@ close Tree_frac(tree, f, depth);
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree).left);
            let f_val = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close Tree_frac(tree, f, depth);
            left_product.wrapping_mul(f_val).wrapping_mul(right_product)
        }
    }
}

unsafe fn print_u64(value: u64)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        //@ Tree_split(tree);

        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        //@ assert Tree_frac(tree, 1/2, ?depth);

        let product_join_handle = spawn(Tree::compute_product_fibs, tree);

        let sum = join(sum_join_handle);
        //@ assert Tree_frac(tree, 1/2, depth);

        let product = join(product_join_handle);
        //@ assert Tree_frac(tree, 1/2, depth);

        //@ Tree_merge(tree);

        print_u64(sum);
        print_u64(product);
    }
}