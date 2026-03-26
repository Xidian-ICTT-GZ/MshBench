use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

predicate tree(*mut Tree t; i32 v) =
    t == null ?
        emp
    :
        exists(*mut Tree left, *mut Tree right, i32 val).
            t |-> struct Tree { left: left, right: right, value: val } *
            tree(left, ?v1) *
            tree(right, ?v2);

predicate fold_data(*mut FoldData d; *mut Tree t, FoldFunction f, i32 a) =
    d |-> struct FoldData { thread: _, tree: t, f: f, acc: a };

predicate_ctor tree_dispose_perm()();

lemma void tree_dispose_lemma()
    req tree(?t, ?v);
    ens emp;

#[requires(tree(t, _))]
#[ensures(emp)]
unsafe fn random_int(max: i32) -> i32 {
    max - 1 
}

predicate fac_inv(i32 x, i32 result, i32 orig_x) =
    x >= 1 &*& result * fac_aux(x) == fac_aux(orig_x);

fixpoint i32 fac_aux(i32 n) {
    n <= 1 ? 1 : n * fac_aux(n - 1)
}

#[requires(true)]
#[ensures(result == fac_aux(x))]
unsafe fn fac(mut x: i32) -> i32 {
    let mut result = 1;
    #[invariant(fac_inv(x, result, old(x)))]
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
    #[ensures(tree(result, _))]
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

    #[requires(tree(tree, _))]
    #[ensures(emp)]
    unsafe fn dispose(tree: *mut Tree) {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    #[requires(tree(tree, _) &*& true)]
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

#[requires(tree(tree, _) &*& f as *const () != null)]
#[ensures(fold_data(result, tree, f, acc))]
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

#[requires(fold_data(data, ?t, ?f, ?a))]
#[ensures(tree(t, _) &*& result == ?final_acc)]
unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    platform::threading::join((*data).thread);
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

#[requires(true)]
#[ensures(result == acc + fac_aux(x))]
unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    acc + fac(x)
}

#[requires(true)]
#[ensures(result == acc ^ fac_aux(x))]
unsafe fn xor_function(acc: i32, x: i32) -> i32 {
    acc ^ fac(x)
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_i32(value: i32) {
    println!("{}", value);
}

#[requires(true)]
#[ensures(true)]
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

#[requires(fold_data(data, ?t, ?f, ?a) &*& tree(t, _))]
#[ensures(fold_data(data, t, f, ?result_acc))]
unsafe fn folder(data: *mut FoldData) {
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}