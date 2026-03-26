//@ req true;
//@ ens true;
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}

struct Node {
    next: *mut Node,
    value: i32,
}

/*@ pred node(n: *mut Node, v: i32, next: *mut Node) =
    n != 0 &*& struct_Node_padding(n) &*&
    *n as *mut i32 |-> ?next_field &*&
    *(n as *mut i8 + 8) as *mut i32 |-> v &*&
    next_field == next;
@*/

/*@ pred stack(s: *mut Stack, nodes: list<*mut Node>) =
    s != 0 &*& struct_Stack_padding(s) &*&
    *s as *mut *mut Node |-> ?head &*&
    if head == 0 then nodes == nil else
        head != 0 &*& nodes == cons(head, ?rest) &*&
        node(head, ?v, ?next) &*&
        stack_nodes(next, rest);
@*/

/*@ fixpoint bool is_nil(list<t> l) { return l == nil; } @*/

/*@ pred stack_nodes(n: *mut Node, nodes: list<*mut Node>) =
    if n == 0 then nodes == nil else
        n != 0 &*& nodes == cons(n, ?rest) &*&
        node(n, ?v, ?next) &*& stack_nodes(next, rest);
@*/

unsafe fn stack_get_count(stack: *mut Stack) -> i32
//@ req stack(stack, ?nodes);
//@ ens stack(stack, nodes) &*& result == length(nodes);
{
    
    let mut n = (*stack).head;
    //@ open stack(stack, nodes);
    //@ assert *stack as *mut *mut Node |-> n;
    let mut i = 0;
    //@ close stack_nodes(n, nodes);
    loop {
        //@ inv stack_nodes(n, ?current_nodes) &*& i == length(nodes) - length(current_nodes);
        
        if n.is_null() {
            //@ open stack_nodes(0, current_nodes);
            //@ assert current_nodes == nil;
            break;
        }
        //@ open stack_nodes(n, current_nodes);
        //@ assert current_nodes == cons(n, ?rest);
        n = (*n).next;
        i += 1;
        //@ close stack_nodes(n, rest);
    }
    //@ leak stack_nodes(n, _);
    i
}