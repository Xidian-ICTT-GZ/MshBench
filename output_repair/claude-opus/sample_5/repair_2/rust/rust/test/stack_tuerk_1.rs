use std::ptr;

struct Node {
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

/*@
pred node_list(n: *mut Node; count: i32) =
    if n == 0 as *mut Node {
        count == 0
    } else {
        (*n).next |-> ?next &*& node_list(next, ?rest_count) &*& count == rest_count + 1 &*& count >= 1
    };

pred stack(s: *mut Stack;) =
    (*s).head |-> ?head &*& node_list(head, _);
@*/

/*@
fn_type stack_get_count_pre(stack: *mut Stack) = req stack(stack);
fn_type stack_get_count_post(stack: *mut Stack, result: i32) = ens stack(stack) &*& result >= 0;
@*/

#[verifier::spec]
#[requires(stack(stack))]
#[ensures(stack(stack) &*& result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    //@ open stack(stack);
    let mut n = (*stack).head;
    //@ assert node_list(n, ?total_count);
    let mut i = 0;
    loop {
        //@ inv node_list(n, ?remaining) &*& i >= 0 &*& (*stack).head |-> ?head &*& node_list(head, _) == true
        //@ open node_list(n, remaining);
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    //@ close stack(stack);
    i
}