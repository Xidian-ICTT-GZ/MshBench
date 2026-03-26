struct Node {
    next: *mut Node,
    value: i32,
}

/*@ 
predicate nodes(struct Node *n; int count) =
    n == null ? count == 0 :
    malloc_block_Node(n) &*&
    nodes((*n).next, ?c) &*& count == c + 1;
@*/

struct Stack {
    head: *mut Node,
}

/*@ 
predicate stack(struct Stack *s; int count) =
    malloc_block_Stack(s) &*&
    nodes((*s).head, count);
@*/

//@ req stack(s, ?count);
//@ ens 0 <= result && result == count;
unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open stack(stack, ?count);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ open nodes(n, ?c);
    loop {
        //@ inv nodes(n, ?c) &*& i as int == count - c;
        
        if n.is_null() {
            //@ close nodes(n, 0);
            break;
        }

        //@ open nodes(n, ?c0);
        n = (*n).next;
        i += 1;
        //@ open nodes(n, ?c1);
        //@ close nodes(n, c1);
    }
    //@ close stack(stack, i);
    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}