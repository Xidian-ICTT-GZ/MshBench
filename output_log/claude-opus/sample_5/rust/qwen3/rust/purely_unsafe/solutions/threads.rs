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
pred sendable_pred<T>(t: Sendable<T>;) = true;

lem sendable_move<T>(t: Sendable<T>)
    req sendable_pred(t);
    ens sendable_pred(t);
{
}

fix fib_val(n: u16) -> u64 {
    if n <= 1 { 1 } else { fib_val((n - 1) as u16).wrapping_add(fib_val((n - 2) as u16)) }
}

pred Tree_own(p: *mut Tree, depth: u8;) =
    if p == 0 {
        depth == 0
    } else {
        alloc_block(p as *mut u8, std::alloc::Layout::new_::<Tree>()) &*&
        (*p).left |-> ?left &*&
        (*p).right |-> ?right &*&
        (*p).value |-> ?value &*&
        depth > 0 &*&
        Tree_own(left, (depth - 1) as u8) &*&
        Tree_own(right, (depth - 1) as u8)
    };

pred Tree_own_sum(p: *mut Tree, depth: u8, sum: u64;) =
    if p == 0 {
        depth == 0 &*& sum == 0
    } else {
        alloc_block(p as *mut u8, std::alloc::Layout::new_::<Tree>()) &*&
        (*p).left |-> ?left &*&
        (*p).right |-> ?right &*&
        (*p).value |-> ?value &*&
        depth > 0 &*&
        Tree_own_sum(left, (depth - 1) as u8, ?lsum) &*&
        Tree_own_sum(right, (depth - 1) as u8, ?rsum) &*&
        sum == lsum.wrapping_add(fib_val(value)).wrapping_add(rsum)
    };

pred join_handle_pred<R>(h: JoinHandle<Sendable<R>>, post: pred(R);) = 
    std::thread::JoinHandle_own(h, sendable_post::<R>(post));

pred_ctor sendable_post<R>(post: pred(R))(r: Sendable<R>) = post(r.payload);

pred tree_sum_post(sum: u64;) = true;

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

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
//@ req std::thread::JoinHandle_own(h, ?post);
//@ ens post(Sendable { payload: result });
{
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens result == fib_val(n);
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop
        //@ inv 2 <= k &*& k <= n &*& fib_k == fib_val(k) &*& fib_k_minus_1 == fib_val((k - 1) as u16);
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
    //@ ens Tree_own(result, depth);
    {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make((depth - 1) as u8);
            let right = Self::make((depth - 1) as u8);
            let value: u16 = 5000;
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close_struct(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close Tree_own(t, depth);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree_own(tree, ?d);
    //@ ens Tree_own_sum(tree, d, result);
    {
        if tree.is_null() {
            //@ close Tree_own_sum(tree, d, 0);
            0
        } else {
            //@ open Tree_own(tree, d);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);

            let result = left_sum.wrapping_add(f).wrapping_add(right_sum);
            //@ close Tree_own_sum(tree, d, result);
            result
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
        //@ open Tree_own(tree, 22);
        let left = (*tree).left;
        let right = (*tree).right;
        let root_val = (*tree).value;

        //@ assert Tree_own(left, 21);
        //@ assert Tree_own(right, 21);

        let left_join_handle = std::thread::spawn(move || {
            //@ open thread_token(?t);
            let result = Tree::compute_sum_fibs(left);
            result
        });

        let right_join_handle = std::thread::spawn(move || {
            //@ open thread_token(?t);
            let result = Tree::compute_sum_fibs(right);
            result
        });
        
        let root_fib = wrapping_fib(root_val);

        let left_sum = left_join_handle.join().unwrap();

        let right_sum = right_join_handle.join().unwrap();

        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);

        print_u64(sum)
    }
}