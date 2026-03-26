#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

predicate tree(Tree* tree_ptr; u64 sum_fibs, u64 product_fibs) =
    tree_ptr != 0 ?
    
    pointer(tree_ptr, Tree { left: *mut Tree, right: *mut Tree, value: u16 }) &*&
    
    tree((*tree_ptr).left, ?left_sum, ?left_prod) &*&
    
    tree((*tree_ptr).right, ?right_sum, ?right_prod) &*&
    
    (*tree_ptr).value |-> ?v &*&
    
    v == 5000 &*&
    
    sum_fibs == left_sum + wrapping_fib_spec(v) &*&
    product_fibs == left_prod * wrapping_fib_spec(v) * right_prod
    :
    
    sum_fibs == 0 &*& product_fibs == 1 &*& true;

fixpoint u64 wrapping_fib_spec(u16 n) {
    return n <= 1 ? 1 : wrapping_fib_spec(n - 1) + wrapping_fib_spec(n - 2);
}

unsafe fn wrapping_fib(n: u16) -> u64
    #[requires(true)]
    #[ensures(result == wrapping_fib_spec(n))]
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop
            #[invariant(2 <= k <= n && fib_k == wrapping_fib_spec(k) && fib_k_minus_1 == wrapping_fib_spec(k - 1))]
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

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
        #[requires(true)]
        #[ensures(tree(result, _, _))]
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

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
        #[requires(tree(tree, ?sum_fibs, ?_))]
        #[ensures(tree(tree, sum_fibs, _))]
        #[ensures(result == sum_fibs)]
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

    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
        #[requires(tree(tree, _, ?prod_fibs))]
        #[ensures(tree(tree, _, prod_fibs))]
        #[ensures(result == prod_fibs)]
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
}

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
    where A: 'static, R: 'static
    #[requires(true)]
    #[ensures(true)]
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
    #[requires(true)]
    #[ensures(true)]
{
    h.join().unwrap().payload
}

unsafe fn print_u64(value: u64)
    #[requires(true)]
    #[ensures(true)]
{
    println!("{}", value);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        open tree(tree, ?sum_fibs, ?prod_fibs); close tree(tree, sum_fibs, prod_fibs);

        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        let sum = join(sum_join_handle);
        let product = join(product_join_handle);
        print_u64(sum);
        print_u64(product);
    }
}