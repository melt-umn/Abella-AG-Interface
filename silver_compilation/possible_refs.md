

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

