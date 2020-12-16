

# A Prolog Framework for the Rapid Prototyping of Language Processors with Attribute Grammars

Link:  [Here](https://www.sciencedirect.com/science/article/pii/S1571066106004798)

This paper is about a framework they built using Prolog to help
students in their compilers course with prototyping their AG compiler.
They used Prolog Definite Clause Grammars (DCG) to do this.  The
purpose was to allow students to *run* their specifications, so this
focuses on evaluation.  As such, they appear to be compiling away the
AG structure before using Prolog to evaluate the tree.  Thus we do not
want to try something like this for reasoning, since the semantic
encoding is separate from the AG structure.

```
@article{Sierra2006,
  title = "A Prolog Framework for the Rapid Prototyping of Language Processors with Attribute Grammars",
  journal = "Electronic Notes in Theoretical Computer Science",
  volume = "164",
  number = "2",
  pages = "19 - 36",
  year = "2006",
  note = "Proceedings of the Sixth Workshop on Language Descriptions, Tools, and Applications (LDTA 2006)",
  issn = "1571-0661",
  doi = "10.1016/j.entcs.2006.10.002",
  author = "José Luis Sierra and Alfredo Fernández-Valmayor",
  keywords = "attribute grammars, language prototyping framework, education in language processors, Prolog"
}
```


# Compiling circular attribute grammars into Prolog

Link:  [Here](https://ieeexplore.ieee.org/abstract/document/5390178)

This paper is focused on evaluation of an attribute grammar.  It
compiles an attribute grammar into Prolog terms.  Each nonterminal
becomes a relation which relates a piece of syntax to attribute
values.  The clauses of this relation encode the equation relations.

His semantics for attribute grammars with only synthesized attributes
are a lot more complicated than his semantics for attribute grammars
with both inherited and synthesized attributes.  I don't understand
why, unless the latter is not supposed to handle circular attributes,
but I think it does, although he never explicitly says either way.
It's difficult to tell because he is doing evaluation with only
synthesized attributes and compilation to assembly with the other.

The encoding for attribute grammars with both inherited and
synthesized attributes appears to be somewhat similar to the one I
came up with.  I need to keep things more separate to handle
extensibility, but the underlying idea of encoding equations into
relations to ensure they hold is the same.  This lack of separation on
the part of the paper (combined with the assumption that attributes
have actual values), means that all attributes must have values for a
tree to be valid under this encoding.  The separation in our encoding
allows some attributes to have values and others not, as is commonly
done in modern systems.

```
@article{Arbab1986,
  author = "Bijan Arbab",
  journal = "IBM Journal of Research and Development",
  title = "Compiling circular attribute grammars into Prolog",
  year = 1986,
  volume = 30,
  number = 3,
  pages = "294-309",
  doi = "10.1147/rd.303.0294"
}
```


# A Semantic Evaluator Generating System in Prolog

Link:  [Here](https://link.springer.com/chapter/10.1007%2F3-540-50820-1_49)

They build semantic evaluators for attribute grammars in Prolog.
These include lexing and parsing, which we are not concerned with,
since we are only working on abstract syntax trees.

Horrifyingly, their abstract syntax tree is a list of nodes.  Each
node is a fact in the knowledge base, carrying an identifier for the
node, its type, the production building it, a list of attribute
values, and a list of the identifiers of its children.  Having a list
of attribute values is like having a node type.  Attribute equations
are encoded as Prolog clauses with relations to access the attributes
off nodes based on their identifier number.

```
@inproceedings{Henriques1989,
  author = "Henriques, Pedro Rangel",
  editor = "Deransart, P. and Lorho, B. and Ma{\l}uszy{\'{n}}ski, J.",
  title = "A semantic evaluator generating system in prolog",
  booktitle = "Programming Languages Implementation and Logic Programming",
  year = "1989",
  publisher = "Springer Berlin Heidelberg",
  address = "Berlin, Heidelberg",
  pages = "201--218",
  doi = "10.1007/3-540-50820-1_49"
}
```


# Prototyping by using an attribute grammar as a logic program

Link:  [Here](https://link.springer.com/chapter/10.1007/3-540-54572-7_16)

Fun fact:  This paper appears to be typed on a typewriter with
mathematical symbols (set union, lambdas) drawn in with a sharpie.

This turns Grammars of Syntactical Functions (GSF) into Prolog
programs.  A GSF of a restricted form is also an attribute grammar.
As with other papers described here, it has nonterminals be relations
describing the relationships between attributes (the equations), with
attribute values as arguments to the relation itself.

Interestingly, because this is translating GSF into Prolog rather than
any attribute grammar, there is no structure representing the tree.
The attributes are computed as it parses, so to encode a rule like
```
BN ::= L '.' L
```
we get a Prolog rule like
```
BN(<args_BN>) :-
   L(<args_L1>), @('.'), L(<args_L2>), <semantic relations>.
```
where the various sets of arguments are the attribute values for the
trees and the semantic relations describe how the attribute values are
related.

```
@inproceedings{Riedewald1991,
  author = "Riedewald, G{\"u}nter",
  editor = "Alblas, Henk and Melichar, Bo{\v{r}}ivoj",
  title = "Prototyping by using an attribute grammar as a logic program",
  booktitle = "Attribute Grammars, Applications and Systems",
  year = "1991",
  publisher = "Springer Berlin Heidelberg",
  address = "Berlin, Heidelberg",
  pages = "401--437",
  doi = "10.1007/3-540-54572-7_16"
}
```


# Attribute grammar based theorem prover

Link:  [Here](https://www.sciencedirect.com/science/article/abs/pii/0950584988901346)

It turns out that the name is more relevant than the paper.  "Theorem
proving" here is really logical deduction like Prolog (logic
programming).

From a set of logic rules they create syntax rules which don't use any
terminal symbols, then use a parser to build a derivation of a goal.
They evaluate attributes at the same time as they are parsing, so if
their `FLAG` attribute says there is a failure, the parser tries to
find an alternative solution.

It can do a couple of things better than standard Prolog:
* It can recognize contradictions between a current goal and an
  ancestor goal, meaning the ancestor goal must be true based on
  excluded middle.  For example, if you are trying to prove `E` and
  you come across `!E`, one of them must be true.  If `!E` is the last
  thing to prove, it must be `E` by contradiction.  This allows it to
  prove more things than standard Prolog.
* The parser can be extended to not simply do depth-first search and
  thus avoid infinite loops.

```
@article{Panayiotopoulos1988,
  title = "Attribute grammar based theorem prover",
  journal = "Information and Software Technology",
  volume = "30",
  number = "9",
  pages = "553 - 560",
  year = "1988",
  issn = "0950-5849",
  doi = "10.1016/0950-5849(88)90134-6",
  author = "T Panayiotopoulos and G Papakonstantinou and G Stamatopoulos",
  keywords = "software engineering, software tools, attribute grammars, theorem proving",
}
```


# A formalisation of parameterised reference attribute grammars

Link:  [Here](https://dl.acm.org/doi/abs/10.1145/3136014.3136024)  
Code Link:  [Here](https://bitbucket.org/scottbuckley/saigacoq-minor/src/master/)
(This link is different than the one in the paper.  He moved it.)

This work presents a language which is intended to capture the essence
of attribute evaluation schemes without worrying about implementation
details of different systems.  This language is intended to be used
for two orthogonal purposes:
1. Prove different caching schemes do not affect attribute values
2. Model and reason about AG implementations of languages

They show different caching schemes do not affect attribute values by
providing evaluation rules for different schemes then proving that the
attributes in any grammar being evaluated have the same values in
both.

The example in their paper for reasoning about AG implementations of a
language is to show that two Saiga implementations of name analysis
for PicoJava are equivalent by showing that the attributes for what
declaration a name refers to are the same.  They don't give any
details of how they do the proof, just the broad ideas behind it, but
it appears they are doing induction on the structure of the tree.
They do not have higher-order attributes, so the tree structure is
enough.

They have the Saiga language implemented in Coq.  There they have
proven the irrelevance of caching.  However, they have not done a
proof of their property for PicoJava.  They have examples of programs
running, but those appear to be testing numbers of cache steps, not
anything related to their property.

I think trying to use the same Coq implementation of Saiga for
reasoning *about* Saiga evaluation and reasoning about languages
written *in* Saiga was a mistake.  The implementation of PicoJava uses
numbered nodes in the tree rather than a tree structure, and
nonterminal types appear to be identified by number as well.  Without
a clear tree structure, I'm not sure it is possible to write a proof
of a language property, and it certainly is extremely difficult.

```
@inproceedings{Buckley2017,
  author = {Buckley, Scott J. H. and Sloane, Anthony M.},
  title = {A Formalisation of Parameterised Reference Attribute Grammars},
  year = {2017},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  url = {https://doi.org/10.1145/3136014.3136024},
  doi = {10.1145/3136014.3136024},
  booktitle = {Proceedings of the 10th ACM SIGPLAN International Conference on Software Language Engineering},
  pages = {139–150},
  numpages = {12},
  keywords = {name analysis, attribute grammars, small-step operational semantics},
  location = {Vancouver, BC, Canada},
  series = {SLE 2017}
}
```

