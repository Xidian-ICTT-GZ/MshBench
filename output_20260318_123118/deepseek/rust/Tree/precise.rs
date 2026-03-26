#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout, dealloc}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: u16) -> bool {
    unsafe { (*t).left == left && (*t).right == right && (*t).value == value }
}

#[predicate]
fn tree_full(t: *mut Tree) -> bool {
    !t.is_null() && 
    exists![left: *mut Tree, right: *mut Tree, value: u16 | 
        tree_points_to(t, left, right, value) && 
        tree_full(left) && 
        tree_full(right)
    ]
}

#[predicate]
fn tree_frac(p: frac, t: *mut Tree) -> bool {
    !t.is_null() && 
    exists![left: *mut Tree, right: *mut Tree, value: u16 | 
        tree_points_to(t, left, right, value) && 
        tree_frac(p, left) && 
        tree_frac(p, right)
    ]
}

#[predicate]
fn tree_null(t: *mut Tree) -> bool {
    t.is_null()
}

#[predicate]
fn join_handle_points_to<R>(h: JoinHandle<Sendable<R>>, p: frac, t: *mut Tree) -> bool {
    true
}

#[predicate]
fn spawn_pre<A, R>(f: Spawnee<A, R>, arg: A) -> bool {
    exists![p: frac, t: *mut Tree | 
        arg == t && 
        tree_frac(p, t) && 
        f == Tree::compute_sum_fibs || f == Tree::compute_product_fibs
    ]
}

#[predicate]
fn spawn_post<A, R>(f: Spawnee<A, R>, arg: A, result: JoinHandle<Sendable<R>>) -> bool {
    exists![p: frac, t: *mut Tree | 
        arg == t && 
        join_handle_points_to(result, p, t)
    ]
}

#[requires(spawn_pre(f, arg))]
#[ensures(spawn_post(f, arg, result))]
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

#[predicate]
fn join_pre<R>(h: JoinHandle<Sendable<R>>) -> bool {
    exists![p: frac, t: *mut Tree | 
        join_handle_points_to(h, p, t) && 
        p == 1 && 
        tree_full(t)
    ]
}

#[predicate]
fn join_post<R>(h: JoinHandle<Sendable<R>>, result: R) -> bool {
    true
}

#[requires(join_pre(h))]
#[ensures(join_post(h, result))]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    h.join().unwrap().payload
}

#[predicate]
fn fib_pre(n: u16) -> bool {
    true
}

#[predicate]
fn fib_post(n: u16, result: u64) -> bool {
    true
}

#[requires(fib_pre(n))]
#[ensures(fib_post(n, result))]
unsafe fn wrapping_fib(n: u16) -> u64
{
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
    #[predicate]
    fn make_pre(depth: u8) -> bool {
        true
    }

    #[predicate]
    fn make_post(depth: u8, result: *mut Tree) -> bool {
        if depth == 0 {
            tree_null(result)
        } else {
            tree_full(result)
        }
    }

    #[requires(Self::make_pre(depth))]
    #[ensures(Self::make_post(depth, result))]
    unsafe fn make(depth: u8) -> *mut Tree
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

    #[predicate]
    fn compute_sum_fibs_pre(tree: *mut Tree) -> bool {
        exists![p: frac | tree_frac(p, tree)]
    }

    #[predicate]
    fn compute_sum_fibs_post(tree: *mut Tree, result: u64) -> bool {
        exists![p: frac | tree_frac(p, tree)]
    }

    #[requires(Self::compute_sum_fibs_pre(tree))]
    #[ensures(Self::compute_sum_fibs_post(tree, result))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
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
    
    #[predicate]
    fn compute_product_fibs_pre(tree: *mut Tree) -> bool {
        exists![p: frac | tree_frac(p, tree)]
    }

    #[predicate]
    fn compute_product_fibs_post(tree: *mut Tree, result: u64) -> bool {
        exists![p: frac | tree_frac(p, tree)]
    }

    #[requires(Self::compute_product_fibs_pre(tree))]
    #[ensures(Self::compute_product_fibs_post(tree, result))]
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
    #[predicate]
    fn dispose_pre(tree: *mut Tree) -> bool {
        tree_full(tree)
    }

    #[predicate]
    fn dispose_post(tree: *mut Tree) -> bool {
        tree_null(tree)
    }

    #[requires(Self::dispose_pre(tree))]
    #[ensures(Self::dispose_post(tree))]
    unsafe fn dispose(tree: *mut Tree)
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }
}

#[predicate]
fn print_u64_pre(value: u64) -> bool {
    true
}

#[predicate]
fn print_u64_post(value: u64) -> bool {
    true
}

#[requires(print_u64_pre(value))]
#[ensures(print_u64_post(value))]
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}

fn main()
{
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