

# Available Theorems
This document lists the theorems which are included in the interface's
library.  All of these theorems are available by default.  For
convenience, these are sorted by types.



## General
- `symmetry` :  
  `forall A B, A = B -> B = A`



## Decorated Trees
- `attr_unique` :  
  `forall Ty (T : Ty) A V V', T.A = V -> T.A = V' -> V = V'`  
  The `V` and `V'` variables may also be filled in with `<no value>`
  to show that it is impossible both to have a value and no value for
  the same attribute on the same tree.
- `attr_is` :  
  `forall Ty (T : Ty) A V IsATy, T.A = V -> IsATy V`  
  This gives us the appropriate `is` relation for an attribute of a
  primitive type.



## Integers
- `is_integer_eq_or_not` :  
  `forall I1 I2, is_integer I1 -> is_integer I2 -> I1 = I2 \/ (I1 = I2 -> false)`

### Plus
- `plus_integer_unique` :  
  `forall N1 N2 N3 N4, N1 + N2 = N3 -> N1 + N2 = N4 -> N3 = N4`
- `plus_integer_is_integer` :  
  `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 + N2 = N3 -> is_integer N3`
- `plus_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists N3, N1 + N2 = N3`
- `plus_integer_comm` :  
  `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 + N2 = N3 -> N2 + N1 = N3`
- `plus_integer_assoc` :  
  `forall N1 N2 N3 Subtotal Total, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 + N2 = Subtotal -> N3 + Subtotal = Total -> exists Subtotal', N2 + N3 = Subtotal' /\ N1 + Subtotal' = Total`

### Minus
- `minus_integer_unique` :  
  `forall N1 N2 N N', N1 - N2 = N -> N1 - N2 = N' -> N = N'`
- `minus_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists N3, N1 - N2 = N3`
- `minus_integer_is_integer` :  
  `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 - N2 = N3 -> is_integer N3`
- `minus_integer_same` :  
  `forall N, is_integer N -> N - N = 0`
- `minus_integer_0` :  
  `forall N, N - 0 = N`

### Negate
- `negate_integer_unique` :  
  `forall N A B, - N = A -> - N = B -> A = B`
- `negate_integer_total` :  
  `forall N, is_integer N -> exists N', - N = N'`
- `negate_integer_is_integer` :  
  `forall N A, is_integer N -> - N = A -> is_integer A`
- `negate_integer_double` :  
  `forall N A, - N = A -> - A = N`
- `plus_integer_0_result` :  
  `forall A B, A + B = 0 -> - A = B`
- `plus_integer_negatives` :  
  `forall A NA B NB C NC, is_integer A -> is_integer B -> is_integer C -> - A = NA -> - B = NB -> - C = NC -> A = B = C -> NA + NB = NC`

### Multiply
- `multiply_integer_unique` :  
  `forall N1 N2 N N', N1 * N2 = N -> N1 * N2 = N' -> N = N'`
- `multiply_integer_is_integer` :  
  `forall N1 N2 N, is_integer N1 -> is_integer N2 -> N1 * N2 = N -> is_integer N`
- `multiply_integer_is_unique` :  
  `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 * N2 = N3 -> is_integer N3`
- `multiply_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists N, N1 * N2 = N`
- `multiply_integer_0_right` :  
  `forall N, is_integer N -> N * 0 = 0`
- `multiply_integer_1` :  
  `forall A, is_integer A -> 1 * A = A`
- `multiply_integer_0_result` :  
  `forall A B, is_integer A -> is_integer B -> A * B = 0 -> A = 0 \/ B = 0`
- `multiply_integer_-1_negate` :  
  `forall A B, -1 * A = B -> - A = B`
- `multiply_integer_negation` :  
  `forall A B C NA NC, is_integer A -> is_integer B -> - A = NA -> A * B = C -> - C = NC -> NA * B = NC`
- `multiply_integer_comm` :  
  `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 * N2 = N3 -> N2 * N1 = N3`
- `multiply_integer_distribute_over_plus` :  
  `forall N1 N2 AddN1N2 N3 Result, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 + N2 = AddN1N2 -> AddN1N2 * N3 = Result -> exists MulN1N3 MulN2N3, N1 * N3 = MulN1N3 /\ N2 * N3 = MulN2N3 /\ MulN1N3 + MulN2N3 = Result`
- `multiply_integer_assoc` :  
  `forall N1 N2 N3 MulN1N2 Result, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 * N2 = MulN1N2 -> MulN1N2 * N3 = Result -> exists MulN2N3, N2 * N3 = MulN2N3 /\ N1 * MulN2N3 = Result`
- `multiply_integer_undistribute_over_plus` :  
  `forall N1 N2 N3 MulN1N3 MulN2N3 Result, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 * N3 = MulN1N3 -> N2 * N3 = MulN2N3 -> MulN1N3 + MulN2N3 = Result -> exists AddN1N2, N1 + N2 = AddN1N2 /\ AddN1N2 * N3 = Result`

### Less Than
- `less_integer_unique` :  
  `forall N1 N2 B B', N1 < N2 = B -> N1 < N2 = B' -> B = B'`
- `less_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 < N2 = B`
- `less_integer_is_bool` :  
  `forall N1 N2 B, N1 < N2 = B -> is_bool B`

### Less Than or Equal To
- `lesseq_integer_unique` :  
  `forall N1 N2 B B', N1 <= N2 = B -> N1 <= N2 = B' -> B = B'`
- `lesseq_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 <= N2 = B`
- `lesseq_integer_is_bool` :  
  `forall N1 N2 B, N1 <= N2 = B -> is_bool B`
- `eq_to_lesseq_integer` :  
  `forall N, is_integer N -> N <= N = true`
- `less_to_lesseq_integer` :  
  `forall N1 N2, N1 < N2 = true -> N1 <= N2 = true`

### Greater Than
- `greater_integer_unique` :  
  `forall N1 N2 B B', N1 > N2 = B -> N1 > N2 = B' -> B = B'`
- `greater_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 > N2 = B`
- `greater_integer_is_bool` :  
  `forall N1 N2 B, N1 > N2 = B -> is_bool B`

### Greater Than or Equal To
- `greatereq_integer_unique` :  
  `forall N1 N2 B B', N1 >= N2 = B -> N1 >= N2 = B' -> B = B'`
- `greatereq_integer_total` :  
  `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 >= N2 = B`
- `greatereq_integer_is_bool` :  
  `forall N1 N2 B, N1 >= N2 = B -> is_bool B`
- `eq_to_greatereq_integer` :  
  `forall N, is_integer N -> N >= N = true`
- `greater_to_greatereq_integer` :  
  `forall N1 N2, N1 > N2 = true -> N1 >= N2 = true`



## Booleans
- `is_bool_eq_or_not` :  
  `forall B1 B2, is_bool B1 -> is_bool B2 -> B1 = B2 \/ (B1 = B2 -> false)`

### And
- `and_bool_unique` :  
  `forall B1 B2 B B', B1 && B2 = B -> B1 && B2 = B' -> B = B'`
- `and_bool_total` :  
  `forall B1 B2, is_bool B1 -> is_bool B2 -> exists B, B1 && B2 = B`
- `and_bool_is_bool` :  
  `forall B1 B2 B3, is_bool B1 -> is_bool B2 -> B1 && B2 = B3 -> is_bool B3`
- `and_bool_comm` :  
  `forall B1 B2 B3, B1 && B2 = B3 -> B2 && B1 = B3`
- `and_bool_true_left` :  
  `forall B, is_bool B -> true && B = B`
- `and_bool_true_left_eq` :  
  `forall B B', true && B = B' -> B' = B`
- `and_bool_true_right` :  
  `forall B, is_bool B -> B && true = B`
- `and_bool_true_right_eq` :  
  `forall B B', B && true = B' -> B' = B`
- `and_bool_false_left` :  
  `forall B B', false && B = B' -> B' = false`
- `and_bool_false_right` :  
  `forall B B', B && false = B' -> B' = false`
- `and_bool_associative` :  
  `forall B1 B2 B3 BRes1 Result, is_bool B2 -> is_bool B3 -> B1 && B2 = BRes1 -> BRes1 && B3 = Result -> exists BRes2, B2 && B3 = BRes2 /\ B1 && BRes2 = Result`
- `and_bool_idempotent` :  
  `forall B, is_bool B -> B && B = B`

### Or
- `or_bool_unique` :  
  `forall B1 B2 B B', B1 || B2 = B -> B1 || B2 = B' -> B = B'`
- `or_bool_total` :  
  `forall B1 B2, is_bool B1 -> is_bool B2 -> exists B, B1 || B2 = B`
- `or_bool_is_bool` :  
  `is_bool B1 -> is_bool B2 -> B1 || B2 = B3 -> is_bool B3`
- `or_bool_comm` :  
  `forall B1 B2 B3, B1 || B2 = B3 -> B2 || B1 = B3`
- `or_bool_true_left` :  
  `forall B B', true || B = B' -> B' = true`
- `or_bool_true_right` :  
  `forall B B', B || true = B' -> B' = true`
- `or_bool_false_left` :  
  `forall B, is_bool B -> false || B = B`
- `or_bool_false_left_eq` :  
  `forall B B', false || B = B' -> B' = B`
- `or_bool_false_right` :  
  `forall B, is_bool B -> B || false = B`
- `or_bool_false_right_eq` :  
  `forall B B', B || false = B' -> B' = B`
- `or_bool_associative` :  
  `forall B1 B2 B3 BRes1 Result, is_bool B2 -> is_bool B3 -> B1 || B2 = BRes1 -> BRes1 || B3 = Result -> exists BRes2, B2 || B3 = BRes2 /\ B1 || BRes2 = Result`
- `or_bool_idempotent` :  
  `forall B, is_bool B -> B || B = B`

### Not
- `not_bool_unique` :  
  `forall B1 B B', ! B1 = B -> ! B1 B' -> B = B'`
- `not_bool_total` :  
  `forall B, is_bool B -> exists B', ! B = B'`
- `not_bool_is_bool` :  
  `forall B B', ! B = B' -> is_bool B'`
- `not_bool_double_negation` :  
  `forall B B', ! B = B' -> ! B' = B`
- `and_bool_complementation` :  
  `forall B NotB, ! B = NotB -> B && NotB = false`
- `or_bool_complementation` :  
  `forall B NotB, ! B = NotB -> B || NotB = true`

### Distributive Laws
- `and_bool__distribute_over__or` :  
  `forall A B C OrBC Result, is_bool A -> is_bool B -> is_bool C -> B || C = OrBC -> A && OrBC = Result -> exists AndAB AndAC, A && B = AndAB /\ A && C = AndAC /\ AndAB || AndAC = Result`
- `and_bool__undistribute_over__or` :  
  `forall A B C AndAB AndAC Result, is_bool A -> is_bool B -> is_bool C -> A && B = AndAB -> A && C = AndAC -> AndAB || AndAC = Result -> exists OrBC, B || C = OrBC /\ A && OrBC = Result`
- `or_bool__distribute_over__and` :  
  `forall A B C AndBC Result, is_bool A -> is_bool B -> is_bool C -> B && C = AndBC -> A || AndBC = Result -> exists OrAB OrAC, A || B = OrAB /\ A || C = OrAC /\ OrAB && OrAC = Result`
- `or_bool__undistribute_over__and` :  
  `forall A B C OrAB OrAC Result, is_bool A -> is_bool B -> is_bool C -> A || B = OrAB -> A || C = OrAC -> OrAB && OrAC = Result -> exists AndBC, B && C = AndBC /\ A || AndBC = Result`

### DeMorgan Laws
- `DeMorgan__not_bool__and_bool` :  
  `forall A B AndAB Result, is_bool A -> is_bool B -> A && B = AndAB -> ! AndAB = Result -> exists NotA NotB, ! A = NotA /\ ! B = NotB /\ NotA || NotB = Result`
- `DeMorgan__or_bool__not_bool` :  
  `forall A B NotA NotB Result, is_bool A -> is_bool B -> ! A NotA -> ! B NotB -> NotA || NotB = Result -> exists AndAB, A && B = AndAB /\ ! AndAB = Result`
- `DeMorgan__not_bool__or_bool` :  
  `forall A B OrAB Result, is_bool A -> is_bool B -> A || B = OrAB -> ! OrAB = Result -> exists NotA NotB, ! A = NotA /\ ! B = NotB /\ NotA && NotB = Result`
- `DeMorgan__and_bool__not_bool` :  
  `forall A B NotA NotB Result, is_bool A -> is_bool B -> ! A = NotA -> ! B = NotB -> NotA && NotB = Result -> exists OrAB, A || B = OrAB /\ ! OrAB = Result`



## Strings
- `is_string_append` :  
  `forall S1 S2 S3, is_string S1 -> is_string S2 -> S1 ++ S2 = S3 -> is_string S3`
- `is_string_eq_or_not` :  
  `forall S1 S2, is_string S1 -> is_string S2 -> S1 = S2 \/ (S1 = S2 -> false)`



## Lists
- `append_nil_right` :  
  `forall L L', L ++ [] = L' -> L = L'`
- `append_nil_left` :  
  `forall L L', [] ++ L = L' -> L = L'`
- `append_unique` :  
  `forall L1 L2 L3 L3', L1 ++ L2 = L3 -> L1 ++ L2 = L3' -> L3 = L3'`
- `is_list_member` :  
  `forall L E SubRel, is_list SubRel L -> member E L -> SubRel E`
- `is_list_append` :  
  `forall L E SubRel, is_list SubRel L -> member E L -> SubRel E`

