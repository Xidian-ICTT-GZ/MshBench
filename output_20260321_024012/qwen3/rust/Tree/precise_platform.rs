//@ predicate tree(Tree* t; i32 depth) =
//@   t == null ?
//@     depth == 0
//@   :
//@     t->left |-> ?left &*& t->right |-> ?right &*& t->value |-> _ &*&
//@     malloc_block_Tree(t) &*&
//@     tree(left, depth - 1) &*& tree(right, depth - 1) &*& depth > 0;

//@ predicate fold_data(FoldData* d; Tree* t, FoldFunction f, i32 acc) =
//@   d->tree |-> t &*& d->f |-> f &*& d->acc |-> acc &*& malloc_block_FoldData(d);

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

unsafe fn random_int(max: i32) -> i32
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
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
    //@ ens tree(result, depth);
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
    //@ req tree(tree, ?depth);
    //@ ens true;
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req tree(tree, ?depth);
    //@ ens tree(tree, depth);
    {
        if tree.is_null() {
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            acc
        }
    }

}

struct FoldData {
    thread: platform::threading::Thread,
    tree: *mut Tree,
    f: FoldFunction,
    acc: i32,
}

unsafe fn folder(data: *mut FoldData)
//@ req fold_data(data, ?t, ?f, ?acc0) &*& [_]is_FoldFunction(f) &*& tree(t, ?depth);
//@ ens fold_data(data, t, f, ?acc1) &*& tree(t, depth);
{
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req tree(tree, ?depth) &*& [_]is_FoldFunction(f);
//@ ens fold_data(result, tree, f, acc) &*& tree(tree, depth);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;

    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req fold_data(data, ?t, ?f, ?acc0) &*& [_]is_FoldFunction(f) &*& tree(t, ?depth);
//@ ens tree(t, depth);
{
    platform::threading::join((*data).thread);
    
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32)
//@ req true;
//@ ens true;
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