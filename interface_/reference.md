

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
   | `forall A B C, ...` |                                           |
   | `exists A B C, ...` |                                           |
   | `nabla A B C, ...`  |                                           |
   | `F1 /\ F2`          | and                                       |
   | `F1 \/ F2`          | or                                        |
   | `F1 -> F2`          | implies                                   |
   | `true`              | logical truth                             |
   | `false`             | logical false                             |
   | `pred t1 t2 t3`     | meta-level predicate or Silver function   |
   | `t1 = t2`           | equality of terms                         |
   | `t1 + t2 = t3`      | addition                                  |
   | `t1 - t2 = t3`      | subtraction                               |
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

