#[predicate]
fn node_chain(n: *mut Node, len: i32) =
  if len == 0 {
    n.is_null()
  } else {
    !n.is_null() && exists len': i32 :: len' == len - 1 && 
    n->next |-> ?next && node_chain(next, len')
  };

#[predicate]
fn stack_valid(s: *mut Stack, len: i32) =
  s->head |-> ?h && node_chain(h, len);

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[requires(stack_valid(stack, ?len) && len >= 0)]
#[ensures(result == len)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        #[invariant(node_chain(n, len - i) && i >= 0 && i <= len)]
        {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}