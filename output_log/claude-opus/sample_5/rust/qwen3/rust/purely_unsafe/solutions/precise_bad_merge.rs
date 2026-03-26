predicate box_i32(int* p, int v) = p |-> v;

fn allocate_box(v: int) -> int* 
    #[requires(true)]
    #[ensures(box_i32(result, v))]
{
    let b = box v;
    b
}

fn read_box(p: int*) -> int
    #[requires(box_i32(p, ?v))]
    #[ensures(box_i32(p, v) &*& result == v)]
{
    *p
}

fn write_box(p: int*, v: int) 
    #[requires(box_i32(p, _))]
    #[ensures(box_i32(p, v))]
{
    *p = v;
}