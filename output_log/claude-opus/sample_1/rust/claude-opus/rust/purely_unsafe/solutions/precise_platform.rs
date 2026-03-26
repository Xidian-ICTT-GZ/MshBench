use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

/*@
predicate struct_Tree_padding(Tree *t;) = true;
predicate struct_FoldData_padding(FoldData *data;) = true;

pred tree(t: *mut Tree; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        struct_Tree_padding(t) &*&
        alloc_block(t as *mut u8, Layout::new_::<Tree>()) &*&
        tree(left, ?ld) &*&
        tree(right, ?rd) &*&
        depth == 1 + (if ld > rd { ld } else { rd })
    };

pred_ctor fold_data_inv(data: *mut FoldData, tree: *mut Tree, f: FoldFunction)() =
    (*data).tree |-> tree &*&
    (*data).f |-> f &*&
    (*data).acc |-> ?acc &*&
    tree(tree, ?depth);

pred fold_data(data: *mut FoldData; thread: platform::threading::Thread, tree: *mut Tree, f: FoldFunction) =
    (*data).thread |-> thread &*&
    (*data).tree |-> tree &*&
    (*data).f |-> f &*&
    (*data).acc |-> ?acc &*&
    struct_FoldData_padding(data) &*&
    alloc_block(data as *mut u8, Layout::new_::<FoldData>());

pred fold_data_post(data: *mut FoldData; tree: *mut Tree, f: FoldFunction) =
    (*data).thread |-> ?thread &*&
    (*data).tree |-> tree &*&
    (*data).f |-> f &*&
    (*data).acc |-> ?acc &*&
    struct_FoldData_padding(data) &*&
    alloc_block(data as *mut u8, Layout::new_::<FoldData>()) &*&
    tree(tree, ?depth);
@*/

/*@
fn_type FoldFunctionType(f: FoldFunction) = unsafe fn(acc: i32, x: i32) -> i32;
    req true;
    ens true;
@*/

#[requires(max >= 1)]
#[ensures(result >= 0 && result < max)]
unsafe fn random_int(max: i32) -> i32 {
    max - 1
}

#[requires(x >= 1)]
#[ensures(result >= 1)]
unsafe fn fac(mut x: i32) -> i32 {
    let mut result = 1;
    //@ int inv_x = x; int inv_r = result;
    loop
    //@ invariant x >= 1 &*& result >= 1
    {
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
    #[ensures(tree(result, ?d) &*& d == depth)]
    unsafe fn make(depth: i32) -> *mut Tree {
        if depth == 0 {
            //@ close tree(std::ptr::null_mut(), 0);
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
            //@ close tree(t, 1 + (if depth - 1 > depth - 1 { depth - 1 } else { depth - 1 }));
            //@ close tree(t, depth);
            t
        }
    }

    #[requires(tree(tree, ?depth))]
    #[ensures(true)]
    unsafe fn dispose(tree: *mut Tree) {
        //@ open tree(tree, depth);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    #[requires(tree(tree, ?depth))]
    #[ensures(tree(tree, depth))]
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32 {
        //@ open tree(tree, depth);
        if tree.is_null() {
            //@ close tree(tree, depth);
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close tree(tree, depth);
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

#[requires((*data).tree |-> ?tree
    &*& (*data).f |-> ?f
    &*& (*data).acc |-> ?acc
    &*& tree(tree, ?depth))]
#[ensures((*data).tree |-> tree
    &*& (*data).f |-> f
    &*& (*data).acc |-> ?new_acc
    &*& tree(tree, depth))]
unsafe fn folder(data: *mut FoldData) {
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

#[requires(tree(tree, ?depth))]
#[ensures(fold_data_post(result, tree, f))]
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData {
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;

    //@ close fold_data_post(data, tree, f);
    data
}

#[requires(fold_data_post(data, ?tree, ?f))]
#[ensures(tree(tree, ?depth))]
unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    //@ open fold_data_post(data, tree, f);
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

#[requires(true)]
#[ensures(true)]
unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    acc + fac(if x >= 1 { x } else { 1 })
}

#[requires(true)]
#[ensures(true)]
unsafe fn xor_function(acc: i32, x: i32) -> i32 {
    acc ^ fac(if x >= 1 { x } else { 1 })
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_i32(value: i32) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(21);

        let sum_data = start_fold_thread(tree, sum_function, 0);

        let sum = join_fold_thread(sum_data);
        Tree::dispose(tree);
        print_i32(sum);
    }
}