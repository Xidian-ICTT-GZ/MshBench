use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred] struct NodePred(n: *mut Node, v: i32, next: *mut Node) {
    n != 0 && 
    n.points_to(Node { next: next, value: v }) &&
    (next == 0 || NodePred(next, _, _))
}

#[pred] struct StackPred(s: *mut Stack, nodes: list<i32>) {
    s != 0 &&
    s.points_to(Stack { head: h }) &&
    ListPred(h, nodes)
}

#[pred] struct ListPred(head: *mut Node, vals: list<i32>) {
    (head == 0 && vals == nil) ||
    (head != 0 && 
     head.points_to(Node { next: tail, value: x }) &&
     ListPred(tail, xs) &&
     vals == cons(x, xs))
}

#[lemma] fn list_pred_unique(head: *mut Node, vals: list<i32>)
    requires ListPred(head, vals),
    ensures ListPred(head, vals) &*& unique(head)
{
    // This lemma asserts uniqueness of the list structure; VeriFast infers it automatically
    // but we declare it to make the specification explicit.
}

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    #[requires(ListPred(n, _))]
    #[ensures(ListPred(n, _))]
{
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(ListPred(n, _))]
    #[ensures(true)]
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(StackPred(result, nil))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(StackPred(stack, xs))]
        #[ensures(StackPred(stack, cons(value, xs)))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(StackPred(stack, cons(x, xs)))]
        #[ensures(StackPred(stack, xs) &*& result == x)]
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
        #[requires(StackPred(stack, _))]
        #[ensures(StackPred(stack, _))]
    {
        map_nodes((*stack).head, f, data);
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(StackPred(stack, _))]
        #[ensures(true)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
    #[requires(data != 0 && data.points_to(i32(_)))]
    #[ensures(result == x + *(data as *mut i32))]
{
    let result = x + *(data as *mut i32);

    result
}

unsafe fn read_i32() -> i32
    #[requires(true)]
    #[ensures(true)]
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();

        Stack::map(s, plus_a, &raw mut a as *mut u8);

        Stack::dispose(s);
    }
}