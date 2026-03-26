#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: u16) -> bool {
    struct_pred!(Tree { left, right, value }) && 
    t != std::ptr::null_mut() &&
    alloc_block(t, std::mem::size_of::<Tree>())
}

#[predicate]
fn tree_null(t: *mut Tree) -> bool {
    t == std::ptr::null_mut()
}

#[predicate]
fn tree(t: *mut Tree) -> bool {
    tree_null(t) || exists![left: *mut Tree, right: *mut Tree, value: u16; tree_points_to(t, left, right, value)]
}

#[predicate]
fn tree_full(t: *mut Tree) -> bool {
    tree(t) && 
    if tree_null(t) {
        true
    } else {
        exists![left: *mut Tree, right: *mut Tree, value: u16; 
            tree_points_to(t, left, right, value) && 
            tree_full(left) && 
            tree_full(right)
        ]
    }
}

#[predicate]
fn tree_frac(p: frac, t: *mut Tree) -> bool {
    tree_null(t) || exists![left: *mut Tree, right: *mut Tree, value: u16; 
        tree_points_to(t, left, right, value) && 
        tree_frac(p, left) && 
        tree_frac(p, right)
    ]
}

#[predicate]
fn join_handle_sendable<R>(h: JoinHandle<Sendable<R>>, p: *mut Tree) -> bool {
    exists![f: Spawnee<*mut Tree, u64>, r: R;
        tree_full(p) && 
        r == f(p) &&
        h.is_join_handle_for(move || Sendable { payload: f(p) })
    ]
}

#[predicate]
fn join_handle_sendable_joined<R>(h: JoinHandle<Sendable<R>>, result: R) -> bool {
    h.join_result() == Ok(Sendable { payload: result })
}

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    #[requires(tree_full(arg))]
    #[ensures(|result| join_handle_sendable(result, arg))]
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    #[requires(|h| exists![p: *mut Tree; join_handle_sendable(h, p)])]
    #[ensures(|result, h| join_handle_sendable_joined(h, result))]
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
{
    #[requires(true)]
    #[ensures(|result| true)]
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_k == wrapping_fib(k) && fib_k_minus_1 == wrapping_fib(k - 1))]
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
        #[ensures(|result| tree_full(result))]
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
        #[requires(tree_full(tree))]
        #[ensures(|result| true)]
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
        let left = (*tree).left;
        let right = (*tree).right;
        
        #[assert(tree_full(tree))]
        #[assert(tree_full(left))]
        #[assert(tree_full(right))]
        
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);
        let right_sum = join(right_join_handle);
        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);
        
        print_u64(sum)
    }
}