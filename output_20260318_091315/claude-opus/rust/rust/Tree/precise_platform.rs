use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

/*@

pred Tree(t: *mut Tree; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        depth > 0 &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        struct_Tree_padding(t) &*&
        Tree(left, depth - 1) &*&
        Tree(right, depth - 1)
    };

pred Tree_frac(t: *mut Tree; depth: i32, frac: real) =
    if t == 0 {
        depth == 0
    } else {
        depth > 0 &*&
        [frac](*t).left |-> ?left &*&
        [frac](*t).right |-> ?right &*&
        [frac](*t).value |-> ?value &*&
        [frac]struct_Tree_padding(t) &*&
        Tree_frac(left, depth - 1, frac) &*&
        Tree_frac(right, depth - 1, frac)
    };

pred FoldData(d: *mut FoldData; tree: *mut Tree, f: FoldFunction, acc: i32) =
    (*d).thread |-> ?thread &*&
    (*d).tree |-> tree &*&
    (*d).f |-> f &*&
    (*d).acc |-> acc &*&
    struct_FoldData_padding(d);

pred FoldData_pre(d: *mut FoldData, depth: i32, frac: real) =
    (*d).tree |-> ?tree &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc &*&
    struct_FoldData_padding(d) &*&
    Tree_frac(tree, depth, frac) &*&
    is_FoldFunction(f);

pred FoldData_post(d: *mut FoldData, depth: i32, frac: real) =
    (*d).tree |-> ?tree &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc &*&
    struct_FoldData_padding(d) &*&
    Tree_frac(tree, depth, frac) &*&
    is_FoldFunction(f);

pred_ctor folder_pre(d: *mut FoldData, depth: i32, frac: real)() =
    FoldData_pre(d, depth, frac);

pred_ctor folder_post(d: *mut FoldData, depth: i32, frac: real)() =
    FoldData_post(d, depth, frac);

pred is_FoldFunction(f: FoldFunction) = true;

lem Tree_to_frac(t: *mut Tree)
    req Tree(t, ?depth);
    ens Tree_frac(t, depth, 1r);
{
    if t == 0 {
    } else {
        open Tree(t, depth);
        Tree_to_frac((*t).left);
        Tree_to_frac((*t).right);
        close Tree_frac(t, depth, 1r);
    }
}

lem Tree_frac_split(t: *mut Tree)
    req Tree_frac(t, ?depth, ?frac);
    ens Tree_frac(t, depth, frac/2) &*& Tree_frac(t, depth, frac/2);
{
    if t == 0 {
        open Tree_frac(t, depth, frac);
        close Tree_frac(t, depth, frac/2);
        close Tree_frac(t, depth, frac/2);
    } else {
        open Tree_frac(t, depth, frac);
        Tree_frac_split((*t).left);
        Tree_frac_split((*t).right);
        close Tree_frac(t, depth, frac/2);
        close Tree_frac(t, depth, frac/2);
    }
}

lem Tree_frac_merge(t: *mut Tree)
    req Tree_frac(t, ?depth, ?frac1) &*& Tree_frac(t, depth, ?frac2);
    ens Tree_frac(t, depth, frac1 + frac2);
{
    if t == 0 {
        open Tree_frac(t, depth, frac1);
        open Tree_frac(t, depth, frac2);
        close Tree_frac(t, depth, frac1 + frac2);
    } else {
        open Tree_frac(t, depth, frac1);
        open Tree_frac(t, depth, frac2);
        Tree_frac_merge((*t).left);
        Tree_frac_merge((*t).right);
        close Tree_frac(t, depth, frac1 + frac2);
    }
}

lem Tree_from_frac(t: *mut Tree)
    req Tree_frac(t, ?depth, 1r);
    ens Tree(t, depth);
{
    if t == 0 {
        open Tree_frac(t, depth, 1r);
        close Tree(t, depth);
    } else {
        open Tree_frac(t, depth, 1r);
        Tree_from_frac((*t).left);
        Tree_from_frac((*t).right);
        close Tree(t, depth);
    }
}

@*/

unsafe fn random_int(max: i32) -> i32
//@ req max > 0;
//@ ens result >= 0 &*& result < max;
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
//@ req x >= 1;
//@ ens true;
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

    unsafe fn make(depth: i32) -> *mut Tree
    //@ req depth >= 0;
    //@ ens Tree(result, depth);
    {
        if depth == 0 {
            //@ close Tree(std::ptr::null_mut(), 0);
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

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree, ?depth);
    //@ ens true;
    {
        //@ open Tree(tree, depth);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req Tree_frac(tree, ?depth, ?frac) &*& is_FoldFunction(f);
    //@ ens Tree_frac(tree, depth, frac) &*& is_FoldFunction(f);
    {
        //@ open Tree_frac(tree, depth, frac);
        if tree.is_null() {
            //@ close Tree_frac(tree, depth, frac);
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close Tree_frac(tree, depth, frac);
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
//@ req FoldData_pre(data, ?depth, ?frac);
//@ ens FoldData_post(data, depth, frac);
{
    //@ open FoldData_pre(data, depth, frac);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close FoldData_post(data, depth, frac);
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req Tree_frac(tree, ?depth, ?frac) &*& is_FoldFunction(f);
//@ ens (*result).thread |-> ?t &*& platform::threading::JoinHandle(t, folder_post(result, depth, frac));
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    //@ close FoldData_pre(data, depth, frac);
    //@ close folder_pre(data, depth, frac)();
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req (*data).thread |-> ?t &*& platform::threading::JoinHandle(t, folder_post(data, ?depth, ?frac));
//@ ens Tree_frac(?tree, depth, frac) &*& is_FoldFunction(?f);
{
    platform::threading::join((*data).thread);
    //@ open folder_post(data, depth, frac)();
    //@ open FoldData_post(data, depth, frac);
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
        //@ Tree_to_frac(tree);
        //@ Tree_frac_split(tree);
        //@ close is_FoldFunction(sum_function);
        let sum_data = start_fold_thread(tree, sum_function, 0);
        //@ close is_FoldFunction(xor_function);
        let xor_data = start_fold_thread(tree, xor_function, 0);
        let sum = join_fold_thread(sum_data);
        let xor = join_fold_thread(xor_data);
        //@ Tree_frac_merge(tree);
        //@ Tree_from_frac(tree);
        Tree::dispose(tree);
        print_i32(sum - xor);
    }
}