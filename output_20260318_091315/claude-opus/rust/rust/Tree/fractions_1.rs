use std::thread;

#[predicate]
pub predicate Tree_pred(t: *mut Tree, v: u64) = t->Tree { value: v };

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(Tree_pred(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(Tree_pred(tree, v))]
    #[ensures(Tree_pred(tree, v) &*& result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(Tree_pred(tree, v))]
    #[ensures(Tree_pred(tree, v) &*& result == v + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

#[requires(true)]
#[ensures(true)]
fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        #[predicate]
        ghost predicate tree_owned() = Tree_pred(tree, 22);

        
        #[requires(tree_owned())]
        #[ensures(true)]
        fn spawn_sum_thread(tree: *mut Tree) -> thread::JoinHandle<u64>
        {
            thread::spawn(move || {
                
                
                Tree::compute_sum_fibs(tree)
            })
        }

        #[requires(tree_owned())]
        #[ensures(true)]
        fn spawn_product_thread(tree: *mut Tree) -> thread::JoinHandle<u64>
        {
            thread::spawn(move || {
                Tree::compute_product_fibs(tree)
            })
        }

        
        
        
        

        
        

        

        

        #[predicate]
        pub predicate Tree_shared(t: *mut Tree, v: u64, frac: real) = 
            frac > 0 &*& frac <= 1 &*& t->Tree(value: v);

        

        
        open Tree_pred(tree, 22);
        close Tree_shared(tree, 22, 1.0);

        
        
        close Tree_shared(tree, 22, 0.5);
        close Tree_shared(tree, 22, 0.5);

        
        
        
        
        

        
        
        

        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));
        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}