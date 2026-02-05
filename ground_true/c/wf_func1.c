/*@
fixpoint_auto list<int> range(int min, int max)
    decreases max - min;
{
    return min == max ? nil : cons(min, range(min + 1, max));
}

fixpoint int sum(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 + sum(xs0);
    }
}

fixpoint bool all_non_negative(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x0, xs0): return x0 >= 0 && all_non_negative(xs0);
    }
}

lemma void sum_of_range_nonnegative(list<int> xs)
    requires all_non_negative(xs) == true;
    ensures 0 <= sum(xs);
{
    switch (xs) {
        case nil:
            // Base case: the sum of an empty list is 0
            return;
        case cons(x0, xs0):
            // Recursive case: prove that sum(xs0) is non-negative
            sum_of_range_nonnegative(xs0);
            assert 0 <= sum(xs0);
            // Since x0 is non-negative and all elements are non-negative,
            // we can assert the sum of the entire list is non-negative.
            assert 0 <= x0 + sum(xs0);
            return;
    }
}

lemma void count_less_than_sum_of_range(int count, int n)
    requires 0 <= count &*& count < n &*& all_non_negative(range(count, n)) == true;
    ensures count <= sum(range(count, n));
{
    switch(range(count, n)) {
        case nil:
            // This case won't occur because count < n, so range(count, n) is never nil.
            assert false;
        case cons(x0, xs0):
            // Since the range starts at count, x0 == count
            assert x0 == count;
            // Prove that sum(xs0) is non-negative by calling the non-negativity lemma on xs0
            assert all_non_negative(xs0) == true; // Elements in xs0 (range(count + 1, n)) are non-negative
            sum_of_range_nonnegative(xs0);
            assert 0 <= sum(xs0); // Now we know that sum(xs0) is non-negative
            // The sum of the list is x0 + sum(xs0), and since x0 == count,
            // we know that count <= count + sum(xs0) (which is trivially true).
            assert sum(range(count, n)) == count + sum(xs0);
            return;
    }
}
@*/

int sum_of_range(int n)
//@ requires 0 <= n &*& sum(range(0, n)) <= INT_MAX &*& all_non_negative(range(0, n)) == true;
//@ ensures result == sum(range(0, n));
{
    int count = 0;
    int sum = 0;
    while (count != n)
    //@ requires 0 <= count && count <= n &*& all_non_negative(range(count, n)) == true &*& sum + sum(range(count, n)) <= INT_MAX;
    //@ ensures sum == old_sum + sum(range(old_count, n));
    //@ decreases n - count;
    {
        //@ count_less_than_sum_of_range(count, n);
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}