use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred_def NodePred<T>(p: *mut Node<T>, v: T, next: *mut Node<T>)]
/*@
    requires
        p != 0 &*&
        malloc_block_Node(p, sizeof<Node<T>>()) &*&
        struct_Node_layout(p) &*&
        (*p).next |-> next &*&
        (*p).value |-> v;
    ensures
        NodePred(p, v, next);
@*/

#[pred_def StackPredTail<T>(p: *mut Node<T>, nodes: list<*mut Node<T>>)]
/*@
    requires
        (p == 0 &*& nodes == nil) ||
        (p != 0 &*&
         malloc_block_Node(p, sizeof<Node<T>>()) &*&
         struct_Node_layout(p) &*&
         (*p).next |-> ?n &*&
         (*p).value |-> ?v &
         (if n == 0 {
             nodes == cons(p, nil)
         } else {
             nodes == cons(p, ?tail) &*&
             StackPredTail(n, tail)
         }));
    ensures
        StackPredTail(p, nodes);
@*/

#[pred_def StackPred<T>(p: *mut Stack<T>, nodes: list<*mut Node<T>>)]
/*@
    requires
        p != 0 &*&
        malloc_block_Stack(p, sizeof<Stack<T>>()) &*&
        struct_Stack_layout(p) &*&
        (*p).head |-> ?h &
        (if h == 0 {
            nodes == nil
        } else {
            nodes == cons(h, ?tail) &*&
            NodePred(h, ?v1, ?n1) &*&
            StackPredTail(n1, tail)
        });
    ensures
        StackPred(p, nodes);
@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    #[requires(Layout::new::<Stack<T>>().size() > 0)]
    #[ensures(result != 0 &*& StackPred(result, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack != 0 &*& StackPred(stack, ?nodes))]
    #[ensures(stack != 0 &*& StackPred(stack, cons(?n, nodes)) &*& NodePred(n, value, ?next))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(stack != 0 &*& StackPred(stack, ?nodes))]
    #[ensures(result == (nodes == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(stack != 0 &*& StackPred(stack, cons(?n, ?nodes)) &*& NodePred(n, ?v, ?next))]
    #[ensures(stack != 0 &*& StackPred(stack, nodes) &*& result == v)]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(stack != 0 &*& StackPred(stack, ?nodes))]
    #[ensures(stack != 0 &*& StackPred(stack, reverse(nodes)))]
    unsafe fn reverse(stack: *mut Stack<T>) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();

        #[invariant(
            StackPredTail(n, ?list_n) &*&
            StackPredTail(m, ?list_m) &*&
            list_n ++ list_m == nodes &*&
            (n == 0 || (malloc_block_Node(n, sizeof<Node<T>>()) &*& struct_Node_layout(n) &*& (*n).next |-> ?next_n &*& (*n).value |-> ?val_n)) &*&
            (m == 0 || (malloc_block_Node(m, sizeof<Node<T>>()) &*& struct_Node_layout(m) &*& (*m).next |-> ?next_m &*& (*m).value |-> ?val_m))
        )]
        loop {
            if n.is_null() {
                break;
            }
            let next = (*n).next;

            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
    }

    #[requires(stack != 0 &*& StackPred(stack, nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

struct Point {
    x: i32,
    y: i32,
}

#[pred_def PointPred(p: *mut Point, x: i32, y: i32)]
/*@
    requires
        p != 0 &*&
        malloc_block_Point(p, sizeof<Point>()) &*&
        struct_Point_layout(p) &*&
        (*p).x |-> x &*&
        (*p).y |-> y;
    ensures
        PointPred(p, x, y);
@*/

impl Point {
    #[requires(Layout::new::<Point>().size() > 0)]
    #[ensures(result != 0 &*& PointPred(result, x, y))]
    unsafe fn create(x: i32, y: i32) -> *mut Point {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        result
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        std::hint::assert_unchecked(Stack::pop(s) == p1);
        std::hint::assert_unchecked(Stack::pop(s) == p2);
        Stack::dispose(s);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}