/*@ pred stack<T>(stack: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    alloc_block_Stack(stack) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    nodes == match head { null => nil, _ => cons(head, ?tail) } &*&
    stack_nodes(head, tail);
@*/

/*@ pred stack_nodes<T>(current: *mut Node<T>, rest: list<*mut Node<T>>) =
    match current {
        null => rest == nil,
        _ => alloc_block_Node(current) &*&
             struct_Node_padding(current) &*&
             (*current).next |-> ?next &*&
             (*current).value |-> _ &*&
             stack_nodes(next, rest)
    };
@*/

/*@ pred vector(v: *mut Vector, x: i32, y: i32) =
    alloc_block_Vector(v) &*&
    struct_Vector_padding(v) &*&
    (*v).x |-> x &*&
    (*v).y |-> y;
@*/

impl<T> Stack<T> {

    //@ req true;
    //@ ens stack(result, nil);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close stack_nodes(null, nil);
        //@ close stack(stack, nil);
        (*stack).head = std::ptr::null_mut();
        stack
    }

    //@ req stack(stack, ?nodes) &*& vector(value, ?x, ?y) &*& x * x + y * y <= limit * limit;
    //@ ens stack(stack, cons(value, nodes));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack(stack, nodes);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close stack_nodes(n, nodes);
        //@ close stack(stack, cons(n, nodes));
        (*stack).head = n;
    }

    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, nodes) &*& result == (match nodes { nil => true, _ => false });
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack(stack, nodes);
        let head = (*stack).head;
        //@ close stack(stack, nodes);
        let result = head.is_null();
        result
    }

    //@ req stack(stack, cons(node, ?rest)) &*& node != null;
    //@ ens stack(stack, rest) &*& vector(result, ?x, ?y) &*& x * x + y * y <= limit * limit;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack(stack, cons(node, rest));
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open stack_nodes(head, rest);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack(stack, rest);
        result
    }

    //@ req stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

//@ assume_correct
unsafe fn input_char() -> char
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

//@ assume_correct
unsafe fn input_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

//@ assume_correct
unsafe fn output_i32(value: i32)
{
    println!("{}", value);
}

impl Vector {

    //@ req true;
    //@ ens vector(result, x, y) &*& x * x + y * y <= limit * limit;
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector(result, x, y);
        result
    }

}

fn main()
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        //@ close stack(s, nil);

        loop {
            //@ inv stack(s, ?nodes);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}