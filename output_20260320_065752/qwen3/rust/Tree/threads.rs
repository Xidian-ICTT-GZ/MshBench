//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let tree = Tree::make(22);
        
        let left = (*tree).left;
        let right = (*tree).right;
        
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);
        
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);
        
        let right_sum = join(right_join_handle);
        
        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);
        
        print_u64(sum)
    }
}

/*@ pred tree(t: *mut Tree) =
    t == std::ptr::null_mut::<Tree>() ?
        true
    :
        alloc_block_Tree(t) &*&
        struct_Tree_padding(t) &*&
        tree((*t).left) &*&
        tree((*t).right);
@*/

//@ req depth <= 255;
//@ ens tree(result);
unsafe fn Tree::make(depth: u8) -> *mut Tree {
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
        //@ close struct_Tree_padding(t);
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        //@ close tree(t);
        t
    }
}

//@ req tree(tree);
//@ ens true;
unsafe fn Tree::compute_sum_fibs(tree: *mut Tree) -> u64 {
    if tree.is_null() {
        0
    } else {
        //@ open tree(tree);
        let left_sum = Self::compute_sum_fibs((*tree).left);
        let f = wrapping_fib((*tree).value);
        let right_sum = Self::compute_sum_fibs((*tree).right);
        //@ close tree(tree);
        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

//@ req true;
//@ ens true;
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k >= 2 && k <= n + 1;
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

//@ req true;
//@ ens true;
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

//@ req true;
//@ ens true;
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

//@ req true;
//@ ens true;
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}