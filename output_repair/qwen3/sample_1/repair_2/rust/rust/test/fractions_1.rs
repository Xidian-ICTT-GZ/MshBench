use std::thread;

/*@
predicate tree_own(tree: *mut Tree, value: u64) =
    (*tree).value |-> value;

predicate tree_frac(tree: *mut Tree, value: u64, frac: real) =
    [frac](*tree).value |-> value;

lemma void split_fraction<t>(t p, u64 v, real f)
    requires tree_own(p, v) &*& 0 < f &*& f < 1;
    ensures tree_frac(p, v, f) &*& tree_frac(p, v, 1 - f);
{
    open tree_own(p, v);
    close tree_frac(p, v, f);
    close tree_frac(p, v, 1 - f);
}

lemma void join_fraction<t>(t p, u64 v, real f1, real f2)
    requires tree_frac(p, v, f1) &*& tree_frac(p, v, f2) &*& f1 + f2 == 1;
    ensures tree_own(p, v);
{
    open tree_frac(p, v, f1);
    open tree_frac(p, v, f2);
    close tree_own(p, v);
}
@*/

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(tree_own(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(tree_frac(tree, ?val, 1/2))]
    #[ensures(tree_frac(tree, val, 1/2) &*& result == val + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree_frac(tree, ?val, 1/2))]
    #[ensures(tree_frac(tree, val, 1/2) &*& result == val + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

#[requires(true)]
#[ensures(true)]
fn print_u64(val: u64) {
    println!("{}", val);
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let tree = Tree::make(22);
        split_fraction(tree, 22, 1/2);
        
        let sum_join_handle = thread::spawn(move || {
            Tree::compute_sum_fibs(tree)
        });
        
        let product_join_handle = thread::spawn(move || {
            Tree::compute_product_fibs(tree)
        });
        
        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();
        
        print_u64(sum);
        print_u64(product);
        
        join_fraction(tree, 22, 1/2, 1/2);
        std::mem::drop(Box::from_raw(tree));
    }
}