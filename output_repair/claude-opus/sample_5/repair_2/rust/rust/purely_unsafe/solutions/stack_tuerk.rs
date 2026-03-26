struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
predicate node(n: *mut Node, count: i32) =
    n == null ? count == 0 : 
    (exists rest: i32; count == rest + 1 && 
     malloc_block(n, sizeof(Node)) &&
     n.value |-> _ &&
     n.next |-> ?next &&
     node(next, rest));

predicate stack(s: *mut Stack) =
    s != null &&
    malloc_block(s, sizeof(Stack)) &&
    s.head |-> ?h &&
    node(h, _);
@*/

/*@
requires stack(stack);
ensures result >= 0;
@*/
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    /*@
    invariant i >= 0 && node(n, ?remaining) && 
              (exists total: i32; total >= 0 && i + remaining == total);
    @*/
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}