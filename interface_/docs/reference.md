

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
   | Formula Syntax       | Meaning                                   |
   -----------------------|--------------------------------------------
   | `forall A B C, ...`  | universal quantification                  |
   | `exists A B C, ...`  | existential quantification                |
   | `nabla A B C, ...`   | nominal quantification                    |
   | `F1 /\ F2`           | and                                       |
   | `F1 \/ F2`           | or                                        |
   | `F1 -> F2`           | implies                                   |
   | `true`               | logical truth                             |
   | `false`              | logical false                             |
   | `pred t1 t2 t3`      | meta-level predicate                      |
   | `t1 = t2`            | equality of terms                         |
   | `t1 + t2 = t3`       | addition                                  |
   | `t1 - t2 = t3`       | subtraction                               |
   | `- t1 = t2`          | negation                                  |
   | `t1 * t2 = t3`       | multiplication                            |
   | `t1 / t2 = t3`       | division                                  |
   | `t1 mod t2 = t3`     | modular division                          |
   | `t1 ++ t2 = t3`      | append                                    |
   | `t1 < t2 = t3`       | less than                                 |
   | `t1 <= t2 = t3`      | less than or equal to                     |
   | `t1 > t2 = t3`       | greater than                              |
   | `t1 >= t2 = t3`      | greater than or equal to                  |
   | `t1 \|\| t2 = t3`    | Boolean or                                |
   | `t1 && t2 = t3`      | Boolean and                               |
   | `!t1 = t2`           | Boolean negation                          |
   | `T.a = t`            | attribute access, where `T` is a variable |
   | `T.a = <no value>`   | attribute access with no value for `a`    |
   | `f(t1, ..., tn) = t` | Silver function application               |

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
   | `p(t1, ..., tn)`   | production application  |



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
(e.g. `is_integer`, `is_string`).



## Silver Decorated Trees
As our purpose is reasoning about Silver grammars, we also have
facilities for working with attribute accesses on decorated trees.  We
have an attribute access metaterm (`T.a = v`) to get values of
attributes.  We also have a metaterm for attribute accesses where
attributes do not have a value (`T.a = <no value>`).



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
We have many of the same tactics as [Abella][1]. We add two additional
tactics for working with attributes on decorated trees:

`case T.a.`  
This does case analysis on the equation cases for the attribute `a`
which occurs on the tree represented by the variable `T`.  This does
**not** require `T.a` to be in a hypothesis of the form `T.a = V`.
For example, if one wishes to prove `T.a` has a value
(`exists V, T.a = V`), this is a necessary step.

`case_local T.a.`  
Similar to case analysis on attribute equations for normal attributes,
this does case analysis on the equation for the local attribute `a`
which occurs on `T`, as well as the equations for its inherited
attributes.  This will only succeed if a hypothesis of the form
`T = <prod>(<children>)` exists, where the local attribute `a` is
defined in the production `<prod>`.

`case_structure T in H1 with H2.`  
This requires that `H1` be an equality of `T` and a second tree `T'`
(either `T = T'` or `T' = T`) and that `H2` be an equality of `T'` and
a structure built by productions (either `T' = <structure>` or
`<structure> = T'`).  It gives a hypothesis that `T` has the same
structure, but with children of different names which are equal to the
children of the structure.  For instance, if the structure of `T'` is
`prod_plus E1 E2`, we would get three assumptions like the following
where `E3` and `E4` are fresh names:
- `T = prod_plus E3 E4`
- `E3 = E1`
- `E4 = E2`



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
* **clean**:  This determines whether Abella tries to automatically
  clear subgoals.  The default value is `on`, which automatically
  applies `attr_unique` and clears subgoals automatically when
  possible, such as when attributes are assumed to have unequal
  values.  If the value is changed to `off`, the user needs to solve
  all the subgoals manually.  Note that a proof written with `clean`
  set to `on` will not be valid with `clean` set to `off` and vice
  versa.  The main purpose of this option is to allow one to see which
  cases are being handled automatically, and thus it should generally
  be turned on to see what is happening and then turned off without
  actually solving the case oneself, especially when proofs are being
  saved.



[1]: http://abella-prover.org/reference-guide.html

