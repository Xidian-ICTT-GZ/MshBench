use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: i32) -> bool {
    unsafe { (*t).left == left && (*t).right == right && (*t).value == value }
}

#[predicate]
fn tree(t: *mut Tree) -> bool {
    if t.is_null() {
        true
    } else {
        tree_points_to(t, (*t).left, (*t).right, (*t).value) 
        && tree((*t).left) 
        && tree((*t).right)
    }
}

#[predicate]
fn tree_own(t: *mut Tree) -> bool {
    if t.is_null() {
        true
    } else {
        tree_points_to(t, (*t).left, (*t).right, (*t).value) 
        && tree_own((*t).left) 
        && tree_own((*t).right)
    }
}

#[predicate]
fn tree_fraction(t: *mut Tree, p: rational) -> bool {
    if t.is_null() {
        true
    } else {
        tree_points_to(t, (*t).left, (*t).right, (*t).value) 
        && tree_fraction((*t).left, p) 
        && tree_fraction((*t).right, p)
    }
}

#[predicate]
fn fold_data_points_to(d: *mut FoldData, tree: *mut Tree, f: FoldFunction, acc: i32, thread: platform::threading::Thread) -> bool {
    unsafe { (*d).tree == tree && (*d).f == f && (*d).acc == acc && (*d).thread == thread }
}

#[predicate]
fn fold_data_own(d: *mut FoldData, tree: *mut Tree, f: FoldFunction, acc: i32, thread: platform::threading::Thread) -> bool {
    fold_data_points_to(d, tree, f, acc, thread)
}

#[requires(max > 0)]
#[ensures(result >= 0 && result < max)]
unsafe fn random_int(max: i32) -> i32 {
    max - 1 
}

#[requires(x >= 1)]
#[ensures(result >= 1)]
unsafe fn fac(mut x: i32) -> i32 {
    let mut result = 1;
    #[invariant(result >= 1)]
    #[invariant(x >= 1)]
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
    #[ensures(result == std::ptr::null_mut() || tree_own(result))]
    unsafe fn make(depth: i32) -> *mut Tree {
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

    #[requires(tree_own(tree))]
    #[ensures(true)]
    unsafe fn dispose(tree: *mut Tree) {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    #[requires(tree_fraction(tree, 1/2))]
    #[ensures(tree_fraction(tree, 1/2))]
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32 {
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

#[requires(fold_data_own(data, tree, f, acc_in, thread))]
#[ensures(fold_data_own(data, tree, f, acc_out, thread))]
unsafe fn folder(data: *mut FoldData) {
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

#[requires(tree_fraction(tree, 1/2))]
#[ensures(fold_data_own(result, tree, f, acc, thread))]
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData {
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

#[requires(fold_data_own(data, tree, f, acc, thread))]
#[ensures(tree_fraction(tree, 1/2))]
unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    platform::threading::join((*data).thread);
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

#[ensures(result == acc + fac(x))]
unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    acc + fac(x)
}

#[ensures(result == acc ^ fac(x))]
unsafe fn xor_function(acc: i32, x: i32) -> i32 {
    acc ^ fac(x)
}

#[ensures(true)]
unsafe fn print_i32(value: i32) {
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