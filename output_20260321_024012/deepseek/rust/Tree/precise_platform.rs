// verifast_options{}

use std::alloc::{Layout, alloc, handle_alloc_error};

unsafe fn random_int(max: i32) -> i32
//@ req true;
//@ ens true;
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
//@ req true;
//@ ens true;
{
    let mut result = 1;
    loop {
        //@ inv true;
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

predicate Tree(t: *mut Tree) {
    alloc::mem::allocated::<Tree>(t) &*&
    struct_Tree_padding(t) &*&
    (*t).left |-> ?left &*&
    (*t).right |-> ?right &*&
    (*t).value |-> ?value &*&
    Tree(left) &*&
    Tree(right)
}

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {
    unsafe fn make(depth: i32) -> *mut Tree
    //@ req depth >= 0;
    //@ ens Tree(result);
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
            //@ close_struct(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close Tree(t);
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree);
    //@ ens true;
    {
        if !tree.is_null() {
            //@ open Tree(tree);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req Tree(tree);
    //@ ens Tree(tree);
    {
        if tree.is_null() {
            acc
        } else {
            //@ open Tree(tree);
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close Tree(tree);
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

predicate FoldData(data: *mut FoldData) {
    alloc::mem::allocated::<FoldData>(data) &*&
    struct_FoldData_padding(data) &*&
    (*data).thread |-> ?thread &*&
    (*data).tree |-> ?tree &*&
    (*data).f |-> ?f &*&
    (*data).acc |-> ?acc &*&
    Tree(tree)
}

unsafe fn folder(data: *mut FoldData)
//@ req FoldData(data);
//@ ens FoldData(data);
{
    //@ open FoldData(data);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close FoldData(data);
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req Tree(tree);
//@ ens FoldData(result);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    //@ close_struct(data);
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    //@ close FoldData(data);
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req FoldData(data);
//@ ens true;
{
    platform::threading::join((*data).thread);
    //@ open FoldData(data);
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