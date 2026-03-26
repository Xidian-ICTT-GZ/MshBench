use std::alloc::{Layout, alloc, handle_alloc_error};

//@ pred dealloc<T>(ptr: *mut u8) = true;

unsafe fn random_int(max: i32) -> i32
//@ req true;
//@ ens true;
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
//@ req x >= 0;
//@ ens result >= 1;
{
    let mut result = 1;
    //@ inv result >= 1 &*& x >= 0;
    loop {
        //@ open true;
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

/*@
pred tree(t: *mut Tree; depth: i32) =
    if t.is_null() {
        depth == 0
    } else {
        alloc_block(t, std::mem::size_of::<Tree>()) &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        tree(left, depth - 1) &*&
        tree(right, depth - 1) &*&
        depth > 0
    };
@*/

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {
    unsafe fn make(depth: i32) -> *mut Tree
    //@ req depth >= 0;
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
    //@ req tree(tree, _);
    //@ ens true;
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            //@ open tree(tree, _);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req tree(tree, _);
    //@ ens true;
    {
        if tree.is_null() {
            acc
        } else {
            //@ open tree(tree, _);
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

/*@
pred folddata(data: *mut FoldData; tree: *mut Tree, f: FoldFunction, acc: i32) =
    alloc_block(data, std::mem::size_of::<FoldData>()) &*&
    (*data).thread |-> ?thread &*&
    (*data).tree |-> tree &*&
    (*data).f |-> f &*&
    (*data).acc |-> acc;
@*/

unsafe fn folder(data: *mut FoldData)
//@ req folddata(data, ?tree, ?f, ?acc) &*& tree(tree, _);
//@ ens true;
{
    //@ open folddata(data, tree, f, acc);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close folddata(data, tree, f, acc);
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req tree(tree, _);
//@ ens folddata(result, tree, f, acc);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    //@ close folddata(data, tree, f, acc);
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    //@ open folddata(data, tree, f, acc);
    //@ close folddata(data, tree, f, acc);
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req folddata(data, _, _, _);
//@ ens true;
{
    platform::threading::join((*data).thread);
    //@ open folddata(data, _, _, _);
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
        //@ assert tree(tree, 21);
        
        let sum_data = start_fold_thread(tree, sum_function, 0);
        //@ assert folddata(sum_data, tree, sum_function, 0);
        
        let xor_data = start_fold_thread(tree, xor_function, 0);
        //@ assert folddata(xor_data, tree, xor_function, 0);
        let sum = join_fold_thread(sum_data);
        let xor = join_fold_thread(xor_data);
        Tree::dispose(tree);
        print_i32(sum - xor);
    }
}