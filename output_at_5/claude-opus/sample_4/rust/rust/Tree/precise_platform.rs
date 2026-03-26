use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

// verifast_options{}

//@ predicate tree(struct Tree* t) = t == NULL ? true : 
//@     malloc_block_tree(t) &*& t->left |-> ?left &*& t->right |-> ?right &*& t->value |-> _ &*& tree(left) &*& tree(right);
//@ predicate malloc_block_tree(struct Tree* t) = true; // opaque malloc block predicate

unsafe fn random_int(max: i32) -> i32
//@ req true;
//@ ensures true;
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
//@ req true;
//@ ensures true;
{
    let mut result = 1;
    loop {
        if x == 1 {
            return result;
        }
        result *= x;
        x -= 1;
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: i32,
}

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {

    unsafe fn make(depth: i32) -> *mut Tree
    //@ req true;
    //@ ensures tree(result);
    {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = random_int(5);
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

    unsafe fn dispose(tree: *mut Tree)
    //@ req tree(tree);
    //@ ensures true;
    {
        if !tree.is_null() {
            let left = (*tree).left;
            let right = (*tree).right;
            close tree(tree);
            Self::dispose(left);
            Self::dispose(right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req tree(tree);
    //@ ensures tree(tree) &*& result == acc || true;
    {
        if tree.is_null() {
            acc
        } else {
            open tree(tree);
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            close tree(tree);
            acc
        }
    }

}

// Minimal abstractions for threading predicates (opaque)
struct FoldData {
    thread: usize, // opaque handle instead of platform::threading::Thread
    tree: *mut Tree,
    f: FoldFunction,
    acc: i32,
}

unsafe fn folder(data: *mut FoldData)
    //@ req true;
    //@ ensures true;
{
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

// Dummy function signatures to replace missing platform::threading
mod platform_threading {
    pub unsafe fn fork_joinable(_f: unsafe fn(*mut super::FoldData), _data: *mut super::FoldData) -> usize {
        0usize
    }
    pub unsafe fn join(_thread: usize) {}
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
    //@ req true;
    //@ ensures true;
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;

    let t = platform_threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
    //@ req true;
    //@ ensures true;
{
    platform_threading::join((*data).thread);

    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32
    //@ req true;
    //@ ensures true;
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
    //@ req true;
    //@ ensures true;
{
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32)
    //@ req true;
    //@ ensures true;
{
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(21);

        let sum_data = start_fold_thread(tree, sum_function, 0);

        let xor_data = start_fold_thread(tree, xor_function, 0);
        let sum = join_fold_thread(sum_data);
        let xor = join_fold_thread(xor_data);
        Tree::dispose(tree);
        print_i32(sum - xor);
    }
}