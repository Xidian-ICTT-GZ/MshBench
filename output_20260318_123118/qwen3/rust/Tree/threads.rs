#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

predicate tree(*mut Tree t; u8 depth) =
    match depth {
        0 => t == std::ptr::null_mut(),
        _ => t != std::ptr::null_mut() && 
             sep(
                 (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> 5000,
                 tree(left, depth - 1),
                 tree(right, depth - 1)
             )
    };

predicate join_handle<Sendable<R>>(JoinHandle<Sendable<R>> h; *mut Tree t, u8 depth) =
    std::thread::join_handle(h, Sendable { payload: ?r }) &*&
    tree(t, depth) &*&
    result(r) == Tree::compute_sum_fibs_result(t);

lemma void compute_sum_fibs_result_lemma(*mut Tree t, u8 depth)
    req tree(t, depth);
    ens result(Tree::compute_sum_fibs_result(t)) == Tree::compute_sum_fibs_spec(t);
{
    if t == std::ptr::null_mut() {
        
    } else {
        let left = (*t).left;
        let right = (*t).right;
        compute_sum_fibs_result_lemma(left, if depth > 0 { depth - 1 } else { 0 });
        compute_sum_fibs_result_lemma(right, if depth > 0 { depth - 1 } else { 0 });
    }
}

fixpoint u64 wrapping_fib_spec(u16 n) {
    match n {
        0 => 1,
        1 => 1,
        _ => wrapping_fib_spec(n - 1) + wrapping_fib_spec(n - 2)
    }
}

fixpoint u64 Tree_compute_sum_fibs_spec(*mut Tree t) {
    if t == std::ptr::null_mut() {
        0
    } else {
        Tree_compute_sum_fibs_spec((*t).left) +
        wrapping_fib_spec((*t).value) +
        Tree_compute_sum_fibs_spec((*t).right)
    }
}

fixpoint u64 Tree_compute_sum_fibs_result(*mut Tree t);

#[requires(depth <= 255)]
#[ensures(match result {
    std::ptr::null_mut() => depth == 0,
    _ => tree(result, depth)
})]
unsafe fn Tree::make(depth: u8) -> *mut Tree
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

#[requires(tree(tree, ?d))]
#[ensures(result == Tree_compute_sum_fibs_spec(tree))]
unsafe fn Tree::compute_sum_fibs(tree: *mut Tree) -> u64
{
    if tree.is_null() {
        0
    } else {
        let left_sum = Self::compute_sum_fibs((*tree).left);
        let f = wrapping_fib((*tree).value);
        let right_sum = Self::compute_sum_fibs((*tree).right);
        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

#[requires(true)]
#[ensures(result == wrapping_fib_spec(n))]
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop 
            #[invariant(k <= n && k >= 2)]
            #[invariant(fib_k == wrapping_fib_spec(k))]
            #[invariant(fib_k_minus_1 == wrapping_fib_spec(k - 1))]
        {
            if k == n { break; }
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

#[requires(tree(arg, ?d))]
#[ensures(join_handle(result, arg, d))]
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

#[requires(join_handle(h, t, d))]
#[ensures(result == Tree_compute_sum_fibs_spec(t))]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    h.join().unwrap().payload
}

#[requires(true)]
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}

fn main()
{
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