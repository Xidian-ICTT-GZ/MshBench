use std::alloc::{Layout, alloc, handle_alloc_error};

/*@
pred tree(t: *mut Tree; depth: i32) =
    if depth == 0 {
        t == std::ptr::null_mut()
    } else {
        alloc_block(t, std::mem::size_of::<Tree>()) &*&
        struct_Tree_padding(t) &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        tree(left, depth - 1) &*&
        tree(right, depth - 1)
    };
@*/

/*@
pred fold_data(data: *mut FoldData; tree: *mut Tree, f: FoldFunction, acc: i32) =
    alloc_block(data, std::mem::size_of::<FoldData>()) &*&
    struct_FoldData_padding(data) &*&
    (*data).thread |-> ?thread &*&
    (*data).tree |-> tree &*&
    (*data).f |-> f &*&
    (*data).acc |-> acc;
@*/

//@ req true;
//@ ens true;
unsafe fn random_int(max: i32) -> i32
{
    max - 1 
}

//@ req true;
//@ ens true;
unsafe fn fac(mut x: i32) -> i32
{
    let mut result = 1;
    //@ inv true;
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
    //@ req depth >= 0;
    //@ ens tree(result, depth);
    unsafe fn make(depth: i32) -> *mut Tree
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
            //@ close tree(t, depth);
            t
        }
    }

    //@ req tree(tree, _);
    //@ ens true;
    unsafe fn dispose(tree: *mut Tree)
    {
        if !tree.is_null() {
            //@ open tree(tree, _);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    //@ req tree(tree, _);
    //@ ens tree(tree, _);
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    {
        if tree.is_null() {
            acc
        } else {
            //@ open tree(tree, _);
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close tree(tree, _);
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

//@ req fold_data(data, tree, f, acc_in);
//@ ens fold_data(data, tree, f, acc_out);
unsafe fn folder(data: *mut FoldData)
{
    //@ open fold_data(data, _, _, _);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close fold_data(data, (*data).tree, (*data).f, acc);
}

//@ req tree(tree, _);
//@ ens fold_data(result, tree, f, acc);
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    //@ close_struct(data);
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    //@ close fold_data(data, tree, f, acc);
    data
}

//@ req fold_data(data, _, _, _);
//@ ens true;
unsafe fn join_fold_thread(data: *mut FoldData) -> i32
{
    platform::threading::join((*data).thread);
    //@ open fold_data(data, _, _, _);
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

//@ req true;
//@ ens true;
unsafe fn sum_function(acc: i32, x: i32) -> i32
{
    acc + fac(x)
}

//@ req true;
//@ ens true;
unsafe fn xor_function(acc: i32, x: i32) -> i32
{
    acc ^ fac(x)
}

//@ req true;
//@ ens true;
unsafe fn print_i32(value: i32)
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