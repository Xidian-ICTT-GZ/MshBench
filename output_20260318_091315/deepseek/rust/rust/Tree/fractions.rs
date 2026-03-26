#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: u16) -> bool {
    unsafe { (*t).left == left && (*t).right == right && (*t).value == value }
}

#[predicate]
fn tree_own(t: *mut Tree) -> bool {
    !t.is_null() && exists![left: *mut Tree, right: *mut Tree, value: u16; tree_points_to(t, left, right, value) && tree_own(left) && tree_own(right)]
}

#[predicate]
fn tree_own_fraction(t: *mut Tree, p: frac) -> bool {
    !t.is_null() && exists![left: *mut Tree, right: *mut Tree, value: u16; tree_points_to(t, left, right, value) && tree_own_fraction(left, p) && tree_own_fraction(right, p)]
}

#[predicate]
fn tree_own_full(t: *mut Tree) -> bool {
    tree_own_fraction(t, 1)
}

#[predicate]
fn tree_own_half(t: *mut Tree) -> bool {
    tree_own_fraction(t, 1/2)
}

#[predicate]
fn tree_own_split(t: *mut Tree) -> bool {
    tree_own_half(t) * tree_own_half(t)
}

#[lemma]
fn tree_own_split_merge(t: *mut Tree)
    requires tree_own_half(t) * tree_own_half(t);
    ensures tree_own_full(t);
{}

#[lemma]
fn tree_own_full_split(t: *mut Tree)
    requires tree_own_full(t);
    ensures tree_own_half(t) * tree_own_half(t);
{}

#[predicate]
fn join_handle_own<R>(h: JoinHandle<Sendable<R>>, p: *mut Tree) -> bool {
    exists![f: Spawnee<*mut Tree, R>; true]
}

#[predicate]
fn sendable_own<R>(s: Sendable<R>) -> bool {
    true
}

#[predicate]
fn arg_own<A>(a: A) -> bool {
    true
}

#[predicate]
fn result_own<R>(r: R) -> bool {
    true
}

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    #[requires(tree_own_full(arg))]
    #[ensures(tree_own_full(arg))]
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    #[requires(join_handle_own(h, tree))]
    #[ensures(tree_own_full(tree))]
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
{
    #[requires(true)]
    #[ensures(true)]
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_k_minus_1 == wrapping_fib(k - 1))]
        #[invariant(fib_k == wrapping_fib(k))]
        loop {
            if k == n { break; }
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
    {
        #[requires(depth >= 0)]
        #[ensures(tree_own_full(result))]
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

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        #[requires(tree_own_full(tree))]
        #[ensures(tree_own_full(tree))]
        if tree.is_null() {
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    {
        #[requires(tree_own_full(tree))]
        #[ensures(tree_own_full(tree))]
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

unsafe fn print_u64(value: u64)
{
    #[requires(true)]
    #[ensures(true)]
    println!("{}", value);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        
        tree_own_full_split(tree);
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        tree_own_full_split(tree);
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        let product = join(product_join_handle);
        
        tree_own_split_merge(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}