use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: i32) -> bool {
    exists![left: *mut Tree, right: *mut Tree, value: i32;
        t != std::ptr::null_mut() &&
        struct_Tree_left(t) == left &&
        struct_Tree_right(t) == right &&
        struct_Tree_value(t) == value
    ]
}

#[predicate]
fn tree(t: *mut Tree) -> bool {
    if t == std::ptr::null_mut() {
        true
    } else {
        tree_points_to(t, struct_Tree_left(t), struct_Tree_right(t), struct_Tree_value(t)) &&
        tree(struct_Tree_left(t)) &&
        tree(struct_Tree_right(t))
    }
}

#[predicate]
fn fold_data_points_to(d: *mut FoldData, tree: *mut Tree, f: FoldFunction, acc: i32, thread: platform::threading::Thread) -> bool {
    exists![tree: *mut Tree, f: FoldFunction, acc: i32, thread: platform::threading::Thread;
        d != std::ptr::null_mut() &&
        struct_FoldData_tree(d) == tree &&
        struct_FoldData_f(d) == f &&
        struct_FoldData_acc(d) == acc &&
        struct_FoldData_thread(d) == thread
    ]
}

#[predicate]
fn fold_data(d: *mut FoldData) -> bool {
    fold_data_points_to(d, struct_FoldData_tree(d), struct_FoldData_f(d), struct_FoldData_acc(d), struct_FoldData_thread(d))
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
    #[invariant(x >= 1)]
    #[invariant(result >= 1)]
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
    #[requires(depth >= 0)]
    #[ensures(tree(result))]
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

    #[requires(tree(tree))]
    #[ensures(true)]
    unsafe fn dispose(tree: *mut Tree) {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    #[requires(tree(tree))]
    #[ensures(true)]
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

#[requires(fold_data(data))]
#[ensures(fold_data(data))]
unsafe fn folder(data: *mut FoldData) {
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

#[requires(tree(tree))]
#[ensures(fold_data(result))]
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

#[requires(fold_data(data))]
#[ensures(true)]
unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    platform::threading::join((*data).thread);
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

#[ensures(true)]
unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    acc + fac(x)
}

#[ensures(true)]
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