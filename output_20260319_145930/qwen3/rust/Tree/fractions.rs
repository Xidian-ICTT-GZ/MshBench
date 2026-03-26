//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let tree = Tree::make(22);
        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        let product = join(product_join_handle);
        
        print_u64(sum);
        print_u64(product);
    }
}

/*@ pred tree(*mut Tree t; u8 depth) =
    t == 0 ?
        depth == 0
    :
        alloc_block_Tree(t) &*&
        struct_Tree_padding(t) &*&
        tree((*t).left, if depth == 0 { 0 } else { depth - 1 }) &*&
        tree((*t).right, if depth == 0 { 0 } else { depth - 1 }) &*&
        (*t).value |-> ?v &*& v == 5000;
@*/

/*@ pred sendable<T>(Sendable<T> s; T payload) = s.payload |-> payload; @*/

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
//@ req true;
//@ ens true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
//@ req true;
//@ ens true;
{
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens true;
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k >= 2 &*& k <= n + 1 &*& true;
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req true;
    //@ ens tree(result, depth);
    {
        if depth == 0 {
            
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; 
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close alloc_block_Tree(t)();
            //@ close struct_Tree_padding(t)();
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, depth);
            
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?d);
    //@ ens tree(tree, d) &*& result >= 0;
    {
        if tree.is_null() {
            0
        } else {
            //@ open tree(tree, _);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree(tree, _);
            
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?d);
    //@ ens tree(tree, d) &*& result >= 0;
    {
        if tree.is_null() {
            1
        } else {
            //@ open tree(tree, _);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close tree(tree, _);
            
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
}

unsafe fn print_u64(value: u64)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}