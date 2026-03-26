struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred nodes(n: *mut Node, count: i32) =
    if n == 0 {
        count == 0
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& alloc_block_Node(n) &*&
        nodes(next, ?c) &*& count == c + 1
    };

pred stack(stack_ptr: *mut Stack, count: i32) =
    (*stack_ptr).head |-> ?h &*& alloc_block_Stack(stack_ptr) &*& nodes(h, count);

@*/

struct Stack {
    head: *mut Node,
}

//@ req stack(stack, ?count);
//@ ens stack(stack, count) &*& result == count;
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open stack(stack, count);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ close nodes(n, count);
    loop {
        //@ inv nodes(n, ?k) &*& i + k == count;

        if n.is_null() {
            //@ open nodes(n, k);
            break;
        }
        //@ open nodes(n, k);
        n = (*n).next;
        i += 1;
        //@ close nodes(n, k - 1);
    }

    //@ close stack(stack, count);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}