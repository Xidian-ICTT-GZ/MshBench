use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

/*@

pred tree(t: *mut Tree) =
    t == std::ptr::null_mut() ?
        true
    :
        alloc_block_Tree(t) &*&
        (*t).left |-> ?l &*& tree(l) &*&
        (*t).right |-> ?r &*& tree(r) &*&
        (*t).value |-> ?v;

pred folddata(d: *mut FoldData) =
    alloc_block_FoldData(d) &*&
    (*d).thread |-> ?th &*&
    (*d).tree |-> ?tr &*& tree(tr) &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc;

@*/

//@ req true;
//@ ens true;
unsafe fn random_int(max: i32) -> i32
{
    max - 1 
}

//@ req x >= 1;
//@ ens true;
unsafe fn fac(mut x: i32) -> i32
{
    let mut result = 1;
    loop {
        //@ inv x >= 1;
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
    //@ ens tree(result);
    unsafe fn make(depth: i32) -> *mut Tree
    {
        if depth == 0 {
            //@ close tree(std::ptr::null_mut());
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
            //@ close tree(t);
            t
        }
    }

    //@ req tree(tree);
    //@ ens true;
    unsafe fn dispose(tree: *mut Tree)
    {
        //@ open tree(tree);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    //@ req tree(tree);
    //@ ens tree(tree);
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    {
        //@ open tree(tree);
        if tree.is_null() {
            //@ close tree(tree);
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close tree(tree);
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

//@ req folddata(data);
//@ ens folddata(data);
unsafe fn folder(data: *mut FoldData)
{
    //@ open folddata(data);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close folddata(data);
}

//@ assume_correct
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req tree(tree);
//@ ens folddata(result);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;

    //@ close folddata(data);
    let t = platform::threading::fork_joinable(folder, data);
    //@ open folddata(data);
    (*data).thread = t;
    //@ close folddata(data);
    data
}

//@ assume_correct
unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req folddata(data);
//@ ens tree(?t) &*& result == ?r;
{
    //@ open folddata(data);
    platform::threading::join((*data).thread);

    let result = (*data).acc;
    let t = (*data).tree;
    //@ close tree(t);
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

//@ req x >= 1;
//@ ens true;
unsafe fn sum_function(acc: i32, x: i32) -> i32
{
    acc + fac(x)
}

//@ req x >= 1;
//@ ens true;
unsafe fn xor_function(acc: i32, x: i32) -> i32
{
    acc ^ fac(x)
}

//@ assume_correct
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