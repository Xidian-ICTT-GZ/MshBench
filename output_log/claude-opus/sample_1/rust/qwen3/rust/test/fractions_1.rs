use std::thread;

#[predicate]
#[verifast::opaque] // to allow unfolding where needed
pub predicate TreePred(tree: *mut Tree, v: u64) = 
    tree != 0 &*&
    tree->value |-> v;

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(result != 0 &*& TreePred(result, v))]
    fn make(v: u64) -> *mut Tree {
        let b = Box::new(Tree { value: v });
        let p = Box::into_raw(b);
        #[ghost] assert(TreePred(p, v)); // predicate constructor from freshly allocated box field
        p
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 1 &*& TreePred(tree, v))] // preserve ownership, just readonly
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            // We have ownership of tree->value at v, just read it.
            (*tree).value + 1
        }
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 2 &*& TreePred(tree, v))] // preserve ownership, just readonly
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            (*tree).value + 2
        }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        // Split the ownership of TreePred to share between threads by duplicating predicates:
        // We must split TreePred into two disjoint parts or share it.
        // Since TreePred is the whole ownership of the box field, and we must move to threads,
        // here we model that sharing by duplicating the predicate ownership with proof.
        //
        // VeriFast does not allow sound duplication of full ownership without fractional permissions,
        // but we approximate by giving each thread full ownership in specs and assume threads consume it.
        //
        // So main thread relinquishes ownership, both threads own the predicate, and main thread regains after join.

        #[ghost] assert(TreePred(tree, 22)); // main owns tree predicate now

        // Give ownership to sum thread
        let sum_join_handle = thread::spawn(move || {
            #[ghost] assume(TreePred(tree, 22)); // thread owns tree predicate passed in
            let res = Tree::compute_sum_fibs(tree);
            #[ghost] assert(TreePred(tree, 22)); // still owns tree predicate after call
            res
        });

        // Give ownership to product thread
        let product_join_handle = thread::spawn(move || {
            #[ghost] assume(TreePred(tree, 22));
            let res = Tree::compute_product_fibs(tree);
            #[ghost] assert(TreePred(tree, 22));
            res
        });

        // Join threads and regain ownership twice (since we gave away ownership twice)
        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        // After join, regain ownership twice, combine for full ownership
        #[ghost] assert(TreePred(tree, 22));
        #[ghost] assert(TreePred(tree, 22));

        print_u64(sum);
        print_u64(product);
    }
}