use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

pred tree(struct Tree* t) = 
    t == std::ptr::null_mut() ? true :
    alloc_block_Tree(t) &*& 
    tree((*t).left) &*& 
    tree((*t).right) &*& 
    pointer(&(*t).left, (*t).left) &*& 
    pointer(&(*t).right, (*t).right) &*& 
    pointer(&(*t).value, _);

@*/

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
    //@ open true;
    loop {
        //@ invariant true;
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
fixpoint layout<Tree>() {
    sizeof<Tree>() == sizeof<*mut Tree>() * 2 + sizeof<i32>();
}
@*/

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {

    //@ req true;
    //@ ensures tree(result);
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
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t);
            t
        }
    }

    //@ req tree(tree);
    //@ ensures true;
    unsafe fn dispose(tree: *mut Tree)
    {
        if !tree.is_null() {
            //@ open tree(tree);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    //@ req tree(tree);
    //@ requires true;
    //@ ensures true;
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    {
        if tree.is_null() {
            acc
        } else {
            //@ open tree(tree);
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

/*@

predicate fold_data(struct FoldData* d) = 
    alloc_block_FoldData(d) &*& 
    pointer(&d->tree, d->tree) &*& 
    pointer(&d->f, d->f) &*& 
    pointer(&d->acc, d->acc) &*& 
    true;

@*/

unsafe fn folder(data: *mut FoldData)
    //@ req fold_data(data) &*& tree((*data).tree);
    //@ ensures fold_data(data);
{
    //@ open fold_data(data);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close fold_data(data);
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
    //@ req tree(tree);
    //@ ensures fold_data(result);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    //@ close fold_data(data);

    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
    //@ req fold_data(data);
    //@ ensures true;
{
    platform::threading::join((*data).thread);
    
    //@ open fold_data(data);
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