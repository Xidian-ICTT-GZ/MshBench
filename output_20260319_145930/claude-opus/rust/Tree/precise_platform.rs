use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Tree(t: *mut Tree; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        alloc_block_Tree(t) &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        Tree(left, ?ld) &*&
        Tree(right, ?rd) &*&
        depth == 1 + ld
    };

pred FoldData_own(d: *mut FoldData;) =
    alloc_block_FoldData(d) &*&
    (*d).thread |-> ?thread &*&
    (*d).tree |-> ?tree &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc;

pred FoldData_pre(d: *mut FoldData;) =
    (*d).tree |-> ?tree &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc &*&
    Tree(tree, ?depth);

pred FoldData_post(d: *mut FoldData;) =
    (*d).tree |-> ?tree &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc &*&
    Tree(tree, ?depth);
@*/

//@ req true;
//@ ens result >= 0 &*& result < max;
unsafe fn random_int(max: i32) -> i32
{
    max - 1 
}

//@ req x >= 1;
//@ ens result >= 1;
unsafe fn fac(mut x: i32) -> i32
{
    let mut result = 1;
    loop {
        //@ inv x >= 1 &*& result >= 1;
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
    //@ ens Tree(result, depth);
    unsafe fn make(depth: i32) -> *mut Tree
    {
        if depth == 0 {
            //@ close Tree(std::ptr::null_mut() as *mut Tree, 0);
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
            //@ close Tree(t, depth);
            t
        }
    }

    //@ req Tree(tree, ?depth);
    //@ ens true;
    unsafe fn dispose(tree: *mut Tree)
    {
        if !tree.is_null() {
            //@ open Tree(tree, depth);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        } else {
            //@ open Tree(tree, depth);
        }
    }

    //@ req Tree(tree, ?depth);
    //@ ens Tree(tree, depth);
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    {
        if tree.is_null() {
            //@ open Tree(tree, depth);
            //@ close Tree(tree, depth);
            acc
        } else {
            //@ open Tree(tree, depth);
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close Tree(tree, depth);
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

//@ req FoldData_pre(data);
//@ ens FoldData_post(data);
unsafe fn folder(data: *mut FoldData)
{
    //@ open FoldData_pre(data);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close FoldData_post(data);
}

//@ req Tree(tree, ?depth);
//@ ens FoldData_own(result) &*& (*result).thread |-> ?t;
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    //@ close FoldData_pre(data);
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    //@ close FoldData_own(data);
    data
}

//@ req FoldData_own(data);
//@ ens true;
unsafe fn join_fold_thread(data: *mut FoldData) -> i32
{
    //@ open FoldData_own(data);
    platform::threading::join((*data).thread);
    //@ open FoldData_post(data);
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

//@ req x >= 0 &*& x < 5;
//@ ens true;
unsafe fn sum_function(acc: i32, x: i32) -> i32
{
    acc + fac(x)
}

//@ req x >= 0 &*& x < 5;
//@ ens true;
unsafe fn xor_function(acc: i32, x: i32) -> i32
{
    acc ^ fac(x)
}

//@ req true;
//@ ens true;
unsafe fn print_i32(value: i32)
{
    //@ assume_correct
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