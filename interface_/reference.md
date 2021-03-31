

# SilverAbella Reference Guide
This guide is based on the [Abella Reference Guide][1].  It is
similarly intended to be a reference for the commands available, not a
tutorial on using SilverAbella.



## Syntax
We have two classes of syntax to concern ourselves with, formulas and
terms.

### Formulas
The syntax of formulas supports many of the same constructs as Abella,
as well as some others:
   | Formula Syntax      | Meaning                                   |
   ----------------------|--------------------------------------------
   | `forall A B C, ...` | universal quantification                  |
   | `exists A B C, ...` | existential quantification                |
   | `nabla A B C, ...`  | nominal quantification                    |
   | `F1 /\ F2`          | and                                       |
   | `F1 \/ F2`          | or                                        |
   | `F1 -> F2`          | implies                                   |
   | `true`              | logical truth                             |
   | `false`             | logical false                             |
   | `pred t1 t2 t3`     | meta-level predicate or Silver function   |
   | `t1 = t2`           | equality of terms                         |
   | `t1 + t2 = t3`      | addition                                  |
   | `t1 - t2 = t3`      | subtraction                               |
   | `- t1 = t2`         | negation                                  |
   | `t1 * t2 = t3`      | multiplication                            |
   | `t1 / t2 = t3`      | division                                  |
   | `t1 mod t2 = t3`    | modular division                          |
   | `t1 ++ t2 = t3`     | append                                    |
   | `t1 < t2 = t3`      | less than                                 |
   | `t1 <= t2 = t3`     | less than or equal to                     |
   | `t1 > t2 = t3`      | greater than                              |
   | `t1 >= t2 = t3`     | greater than or equal to                  |
   | `t1 \|\| t2 = t3`   | Boolean or                                |
   | `t1 && t2 = t3`     | Boolean and                               |
   | `!t1 = t2`          | Boolean negation                          |
   | `T.a = t`           | attribute access, where `T` is a variable |
   | `T.a = <no value>`  | attribute access with no value for `a`    |

Any formulas which include an equals sign may also be flipped about
the equals sign (e.g. `t3 = t1 + t2` is equivalent to `t1 + t2 = t3`).

Identifiers (variables, theorem names, etc.) may begin with a letter
or one of ``-^=`'?`` followed by any letters, digits, symbols from the
previous list, or `$_*@+#!~/`.  If an identifier starts with `=`,
it must be followed by another character.

Single-line comments start with `%` and may begin anywhere in a line.
Multi-line comments are demarcated by `/*` and `*/`.

### Terms
The syntax of terms includes the same constructs as Abella, which are
constants, applications of constants, and abstractions, but it also
adds syntax for literals from Silver:
   | Term Syntax        | Meaning                 |
   ---------------------|--------------------------
   | `<var>`            | variable                |
   | `t1 t2 ... tn`     | constructor application |
   | `t1::t2`           | cons list               |
   | `nil`              | empty list              |
   | `[]`               | empty list              |
   | `[t1, t2, ... tn]` | list literal            |
   | `(t1, t2, ... tn)` | tuple literal           |
   | `"<contents>"`     | string literal          |
   | `<integer>`        | integer literal         |
   | `true`             | Boolean true            |
   | `false`            | Boolean false           |



## Silver Primitive Types
As seen in the above syntax, we have added some primitive and
quasi-primitive types from Silver to our theorem prover.  The Silver
types which have been added are:
* `integer` for `Integer`
* `bool` for `Boolean`
* `string` for `String`
* `pair A B` for `Pair<A B>`, where one can also write n-tuples
  (nested pairs) as `(t1, t2, ... tn)`
* `list A` for `[A]`, using Abella's built-in lists, but adding syntax
  for list literals (`[t1, t2, ... tn]`)

These primitives have appropriate operations defined on them.  For
example, we have an addition metaterm (`t1 + t2 = t3`).  Each of these
types also has an appropriate `is` relation defined
(e.g. `is_integer`, `is_string`).  We also have theorems about the
operations defined on these types:
* `integer` operations:
  + `is_integer_eq_or_not` :  
    `forall I1 I2, is_integer I1 -> is_integer I2 -> I1 = I2 \/ (I1 = I2 -> false)`
  + `plus_integer_unique` :  
    `forall N1 N2 N3 N4, N1 + N2 = N3 -> N1 + N2 = N4 -> N3 = N4`
  + `plus_integer_is_integer` :  
    `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 + N2 = N3 -> is_integer N3`
  + `plus_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists N3, N1 + N2 = N3`
  + `plus_integer_comm` :  
    `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 + N2 = N3 -> N2 + N1 = N3`
  + `plus_integer_assoc` :  
    `forall N1 N2 N3 Subtotal Total, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 + N2 = Subtotal -> N3 + Subtotal = Total -> exists Subtotal', N2 + N3 = Subtotal' /\ N1 + Subtotal' = Total`
  + `minus_integer_unique` :  
    `forall N1 N2 N N', N1 - N2 = N -> N1 - N2 = N' -> N = N'`
  + `minus_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists N3, N1 - N2 = N3`
  + `minus_integer_is_integer` :  
    `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 - N2 = N3 -> is_integer N3`
  + `minus_integer_same` :  
    `forall N, is_integer N -> N - N = 0`
  + `minus_integer_0` :  
    `forall N, N - 0 = N`
  + `negate_integer_unique` :  
    `forall N A B, - N = A -> - N = B -> A = B`
  + `negate_integer_total` :  
    `forall N, is_integer N -> exists N', - N = N'`
  + `negate_integer_is_integer` :  
    `forall N A, is_integer N -> - N = A -> is_integer A`
  + `negate_integer_double` :  
    `forall N A, - N = A -> - A = N`
  + `plus_integer_0_result` :  
    `forall A B, A + B = 0 -> - A = B`
  + `plus_integer_negatives` :  
    `forall A NA B NB C NC, is_integer A -> is_integer B -> is_integer C -> - A = NA -> - B = NB -> - C = NC -> A = B = C -> NA + NB = NC`
  + `multiply_integer_unique` :  
    `forall N1 N2 N N', N1 * N2 = N -> N1 * N2 = N' -> N = N'`
  + `multiply_integer_is_integer` :  
    `forall N1 N2 N, is_integer N1 -> is_integer N2 -> N1 * N2 = N -> is_integer N`
  + `multiply_integer_is_unique` :  
    `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 * N2 = N3 -> is_integer N3`
  + `multiply_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists N, N1 * N2 = N`
  + `multiply_integer_0_right` :  
    `forall N, is_integer N -> N * 0 = 0`
  + `multiply_integer_1` :  
    `forall A, is_integer A -> 1 * A = A`
  + `multiply_integer_0_result` :  
    `forall A B, is_integer A -> is_integer B -> A * B = 0 -> A = 0 \/ B = 0`
  + `multiply_integer_-1_negate` :  
    `forall A B, -1 * A = B -> - A = B`
  + `multiply_integer_negation` :  
    `forall A B C NA NC, is_integer A -> is_integer B -> - A = NA -> A * B = C -> - C = NC -> NA * B = NC`
  + `multiply_integer_comm` :  
    `forall N1 N2 N3, is_integer N1 -> is_integer N2 -> N1 * N2 = N3 -> N2 * N1 = N3`
  + `multiply_integer_distribute_over_plus` :  
    `forall N1 N2 AddN1N2 N3 Result, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 + N2 = AddN1N2 -> AddN1N2 * N3 = Result -> exists MulN1N3 MulN2N3, N1 * N3 = MulN1N3 /\ N2 * N3 = MulN2N3 /\ MulN1N3 + MulN2N3 = Result`
  + `multiply_integer_assoc` :  
    `forall N1 N2 N3 MulN1N2 Result, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 * N2 = MulN1N2 -> MulN1N2 * N3 = Result -> exists MulN2N3, N2 * N3 = MulN2N3 /\ N1 * MulN2N3 = Result`
  + `multiply_integer_undistribute_over_plus` :  
    `forall N1 N2 N3 MulN1N3 MulN2N3 Result, is_integer N1 -> is_integer N2 -> is_integer N3 -> N1 * N3 = MulN1N3 -> N2 * N3 = MulN2N3 -> MulN1N3 + MulN2N3 = Result -> exists AddN1N2, N1 + N2 = AddN1N2 /\ AddN1N2 * N3 = Result`
  + `less_integer_unique` :  
    `forall N1 N2 B B', N1 < N2 = B -> N1 < N2 = B' -> B = B'`
  + `less_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 < N2 = B`
  + `less_integer_is_bool` :  
    `forall N1 N2 B, N1 < N2 = B -> is_bool B`
  + `lesseq_integer_unique` :  
    `forall N1 N2 B B', N1 <= N2 = B -> N1 <= N2 = B' -> B = B'`
  + `lesseq_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 <= N2 = B`
  + `lesseq_integer_is_bool` :  
    `forall N1 N2 B, N1 <= N2 = B -> is_bool B`
  + `eq_to_lesseq_integer` :  
    `forall N, is_integer N -> N <= N = true`
  + `less_to_lesseq_integer` :  
    `forall N1 N2, N1 < N2 = true -> N1 <= N2 = true`
  + `greater_integer_unique` :  
    `forall N1 N2 B B', N1 > N2 = B -> N1 > N2 = B' -> B = B'`
  + `greater_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 > N2 = B`
  + `greater_integer_is_bool` :  
    `forall N1 N2 B, N1 > N2 = B -> is_bool B`
  + `greatereq_integer_unique` :  
    `forall N1 N2 B B', N1 >= N2 = B -> N1 >= N2 = B' -> B = B'`
  + `greatereq_integer_total` :  
    `forall N1 N2, is_integer N1 -> is_integer N2 -> exists B, N1 >= N2 = B`
  + `greatereq_integer_is_bool` :  
    `forall N1 N2 B, N1 >= N2 = B -> is_bool B`
  + `eq_to_greatereq_integer` :  
    `forall N, is_integer N -> N >= N = true`
  + `greater_to_greatereq_integer` :  
    `forall N1 N2, N1 > N2 = true -> N1 >= N2 = true`
* `bool` operations:
  + `and_bool_unique` :  
    `forall B1 B2 B B', B1 && B2 = B -> B1 && B2 = B' -> B = B'`
  + `and_bool_total` :  
    `forall B1 B2, is_bool B1 -> is_bool B2 -> exists B, B1 && B2 = B`
  + `and_bool_is_bool` :  
    `forall B1 B2 B3, is_bool B1 -> is_bool B2 -> B1 && B2 = B3 -> is_bool B3`
  + `and_bool_comm` :  
    `forall B1 B2 B3, B1 && B2 = B3 -> B2 && B1 = B3`
  + `and_bool_true_left` :  
    `forall B, is_bool B -> true && B = B`
  + `and_bool_true_left_eq` :  
    `forall B B', true && B = B' -> B' = B`
  + `and_bool_true_right` :  
    `forall B, is_bool B -> B && true = B`
  + `and_bool_true_right_eq` :  
    `forall B B', B && true = B' -> B' = B`
  + `and_bool_false_left` :  
    `forall B B', false && B = B' -> B' = false`
  + `and_bool_false_right` :  
    `forall B B', B && false = B' -> B' = false`
  + `and_bool_associative` :  
    `forall B1 B2 B3 BRes1 Result, is_bool B2 -> is_bool B3 -> B1 && B2 = BRes1 -> BRes1 && B3 = Result -> exists BRes2, B2 && B3 = BRes2 /\ B1 && BRes2 = Result`
  + `and_bool_idempotent` :  
    `forall B, is_bool B -> B && B = B`
  + `or_bool_unique` :  
    `forall B1 B2 B B', B1 || B2 = B -> B1 || B2 = B' -> B = B'`
  + `or_bool_total` :  
    `forall B1 B2, is_bool B1 -> is_bool B2 -> exists B, B1 || B2 = B`
  + `or_bool_is_bool` :  
    `is_bool B1 -> is_bool B2 -> B1 || B2 = B3 -> is_bool B3`
  + `or_bool_comm` :  
    `forall B1 B2 B3, B1 || B2 = B3 -> B2 || B1 = B3`
  + `or_bool_true_left` :  
    `forall B B', true || B = B' -> B' = true`
  + `or_bool_true_right` :  
    `forall B B', B || true = B' -> B' = true`
  + `or_bool_false_left` :  
    `forall B, is_bool B -> false || B = B`
  + `or_bool_false_left_eq` :  
    `forall B B', false || B = B' -> B' = B`
  + `or_bool_false_right` :  
    `forall B, is_bool B -> B || false = B`
  + `or_bool_false_right_eq` :  
    `forall B B', B || false = B' -> B' = B`
  + `or_bool_associative` :  
    `forall B1 B2 B3 BRes1 Result, is_bool B2 -> is_bool B3 -> B1 || B2 = BRes1 -> BRes1 || B3 = Result -> exists BRes2, B2 || B3 = BRes2 /\ B1 || BRes2 = Result`
  + `or_bool_idempotent` :  
    `forall B, is_bool B -> B || B = B`
  + `not_bool_unique` :  
    `forall B1 B B', ! B1 = B -> ! B1 B' -> B = B'`
  + `not_bool_total` :  
    `forall B, is_bool B -> exists B', ! B = B'`
  + `not_bool_is_bool` :  
    `forall B B', ! B = B' -> is_bool B'`
  + `not_bool_double_negation` :  
    `forall B B', ! B = B' -> ! B' = B`
  + `and_bool_complementation` :  
    `forall B NotB, ! B = NotB -> B && NotB = false`
  + `or_bool_complementation` :  
    `forall B NotB, ! B = NotB -> B || NotB = true`
  + `and_bool__distribute_over__or` :  
    `forall A B C OrBC Result, is_bool A -> is_bool B -> is_bool C -> B || C = OrBC -> A && OrBC = Result -> exists AndAB AndAC, A && B = AndAB /\ A && C = AndAC /\ AndAB || AndAC = Result`
  + `and_bool__undistribute_over__or` :  
    `forall A B C AndAB AndAC Result, is_bool A -> is_bool B -> is_bool C -> A && B = AndAB -> A && C = AndAC -> AndAB || AndAC = Result -> exists OrBC, B || C = OrBC /\ A && OrBC = Result`
  + `or_bool__distribute_over__and` :  
    `forall A B C AndBC Result, is_bool A -> is_bool B -> is_bool C -> B && C = AndBC -> A || AndBC = Result -> exists OrAB OrAC, A || B = OrAB /\ A || C = OrAC /\ OrAB && OrAC = Result`
  + `or_bool__undistribute_over__and` :  
    `forall A B C OrAB OrAC Result, is_bool A -> is_bool B -> is_bool C -> A || B = OrAB -> A || C = OrAC -> OrAB && OrAC = Result -> exists AndBC, B && C = AndBC /\ A || AndBC = Result`
  + `DeMorgan__not_bool__and_bool` :  
    `forall A B AndAB Result, is_bool A -> is_bool B -> A && B = AndAB -> ! AndAB = Result -> exists NotA NotB, ! A = NotA /\ ! B = NotB /\ NotA || NotB = Result`
  + `DeMorgan__or_bool__not_bool` :  
    `forall A B NotA NotB Result, is_bool A -> is_bool B -> ! A NotA -> ! B NotB -> NotA || NotB = Result -> exists AndAB, A && B = AndAB /\ ! AndAB = Result`
  + `DeMorgan__not_bool__or_bool` :  
    `forall A B OrAB Result, is_bool A -> is_bool B -> A || B = OrAB -> ! OrAB = Result -> exists NotA NotB, ! A = NotA /\ ! B = NotB /\ NotA && NotB = Result`
  + `DeMorgan__and_bool__not_bool` :  
    `forall A B NotA NotB Result, is_bool A -> is_bool B -> ! A = NotA -> ! B = NotB -> NotA && NotB = Result -> exists OrAB, A || B = OrAB /\ ! OrAB = Result`
* `string` operations:
  + `is_string_append` :  
    `forall S1 S2 S3, is_string S1 -> is_string S2 -> S1 ++ S2 = S3 -> is_string S3`
  + `is_string_eq_or_not` :  
    `forall S1 S2, is_string S1 -> is_string S2 -> S1 = S2 \/ (S1 = S2 -> false)`
* `list` operations:
  + `append_nil_right` :  
    `forall L L', L ++ [] = L' -> L = L'`
  + `append_nil_left` :  
    `forall L L', [] ++ L = L' -> L = L'`
  + `append_unique` :  
    `forall L1 L2 L3 L3', L1 ++ L2 = L3 -> L1 ++ L2 = L3' -> L3 = L3'`
  + `is_list_member` :  
    `forall L E SubRel, is_list SubRel L -> member E L -> SubRel E`
  + `is_list_append` :  
    `forall L E SubRel, is_list SubRel L -> member E L -> SubRel E`



## Silver Decorated Trees
As our purpose is reasoning about Silver grammars, we also have
facilities for working with attribute accesses on decorated trees.  We
have an attribute access metaterm (`T.a = v`) to get values of
attributes.  We also have a metaterm for attribute accesses where
attributes do not have a value (`T.a = <no value>`).

We have a theorem `attr_unique` to show attribute values are unique on
any given tree:
```
forall Ty (T : Ty) A V V', T.A = V -> T.A = V' -> V = V'
```
The `V` and `V'` variables may also be filled in with `<no value>` to
show that it is impossible both to have a value and no value for the
same attribute on the same tree.  This theorem should rarely need to
be used, since its application is built into the theorem prover.

We also have a theorem `attr_is` to show `is` relations hold for
attributes of primitive and quasi-primitive types:
```
forall Ty (T : Ty) A V IsATy, T.A = V -> IsATy V
```
This gives us the appropriate `is` relation for an attribute (e.g. if
`A` has type `list (pair string integer)` and we have an assumption
`T.A = V`, apply `attr_is` to this assumption would give us
`is_list (is_pair is_string is_integer) V`.  This does not apply to
attributes which do not have a primitive type.



## Top-Level Commands
Most top-level commands are the same as in [Abella][1].  We add one
additional top-level command.

`Extensible_Theorem <name> : <formula> on <names>.`  
`Extensible_Theorem [<depth>] <name> : <formula> on <names>.`  
This introduces a theorem (possibly a mutually-inductive theorem)
which will be proven by induction on the given tree name or names.
If the tree or trees given for induction (after `on`) are not
actually trees, this gives an error.  On success, this puts the
prover into proving mode with a conjunctive goal to prove the
statement for each known production of the correct nonterminal
type with the correct inductive assumptions.



## Tactics
We have many of the same tactics as [Abella][1]. We add one additional
tactic for working with attributes on decorated trees:

`case T.a.`  
This does case analysis on the equation cases for the attribute `a`
which occurs on the tree represented by the variable `T`.  This does
**not** require `T.a` to be in a hypothesis of the form `T.a = V`.
For example, if one wishes to prove `T.a` has a value
(`exists V, T.a = V`), this is a necessary step.



## Common Commands
Abella has three commands common to both the top level and the proving
mode available for users, which we copy.

`Quit.`  
This exists the theorem prover.

`Show <name>.`  
This shows the previously-proven theorem to the user.

`Set <option> <value>.`  
This changes options in how the theorem prover works and displays
information to the user.
* **subgoals**:  This determines how subgoals in an active proof are
  displayed.  The default value is `on`, which prints all subgoals.
  Setting it to `off` simply prints how many subgoals are remaining,
  but does not show what they are.  Giving it a numeric value will
  only show subgoals at that many levels of depth.
* **search_depth**:  This determines the default search depth used by
  the `search` tactic.  The default value is `5`.
* **debug**:  This determines whether the Abella translation of the
  interaction is shown.  The default value is `off`, which displays
  nothing of the translation.  If the value is changed to `on`, it
  will display the command sent to Abella, as well as the output from
  Abella, in addition to the standard output.



[1]: http://abella-prover.org/reference-guide.html

