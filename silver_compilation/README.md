
There are several files here describing our encoding of Silver into
relational systems, primarily Abella:
* [BasicEncoding.md](BasicEncoding.md):  This file describes the basics
  of our encoding, including how we encode decorated trees, attribute
  equations, and well-partially-decorated trees.  All the other files
  assume the material described in this file.
* [PrimitiveTypes.md](PrimitiveTypes.md):  This file describes
  encodings of more primitive and quasi-primitive types from Silver
  into Abella.
* [Functions.md](Functions.md):  This file describes how we encode
  functions and function calls.
* [Locals.md](Locals.md):  This file describes our implementation of
  local attributes, including defining them and their inherited
  attributes.
* [Forwards.md](Forwards.md):  This file describes our implementation
  of forwards and forwarding.  Our encoding of forwards is similar to
  our encoding of locals, so this assumes the information in that
  file.
* [PatternMatching.md](PatternMatching.md):  This file describes
  potential encodings of Silver's pattern matching into relations.
  Nonterminal matching relies on forwarding, so this assumes the
  information in that file.
* [ExtensionAttributes.md](ExtensionAttributes.md):  This file
  describes the scheme for handling extension-introduced attributes.
  These are different than host-introduced attributes because of how
  they are handled in composition in Silver.
* [CompleteEquations.md](CompleteEquations.md):  This file describes
  the details of our complete equation scheme, which ensures we have
  attribute values when possible and that we don't when not possible.

Another related file, but which is not part of the encoding scheme, is
[PossibleRefs.md](PossibleRefs.md).  This file contains notes on and
references to work that is at least somewhat related to what we are
doing here, which might be relevant to cite in a paper.


# Notes for Further Action

There are some things I'm going to want to come back to in these
documents.  I will keep a list here:
* In [Forwards.md](Forwards.md), under the heading "A Raw Alternative
  Formation", I have a raw idea for cleaning up the equations for
  inherited attributes on the forward.  I need to look into this and
  see if it really will make things cleaner.  This also affects the
  copy relations for inherited attributes in
  [ExtensionAttributes.md](ExtensionAttributes.md).
* In [PrimitiveTypes.md](PrimitiveTypes.md), we discuss several
  possible implementations of floating-point numbers.  When we are
  ready to start thinking about these, we should look at CompCert to
  see how they handle them.
* In [ExtensionAttributes.md](ExtensionAttributes.md), we introduce
  the idea of **copy relations** to bring synthesized attributes
  introduced by an extension from the forward to the forwarding tree
  for trees built by productions from other extensions.  These copy
  relations (in the primary formulation) don't include any
  restrictions on what productions they may be used for in the
  component (they are specialized in the composition).  I'm starting
  to question the safety of this.  We might create a relation which
  holds on terms built by productions from other extensions, declared
  in the component introducing the attribute and filled in in the
  composition, then say the copy rule only holds if this relation
  holds on the term.  This would eliminate the need to specialize the
  copy relation in the composition as well.
* In [Locals.md](Locals.md), we note that we can require all known
  inherited attributes for which we do not have an equation to be
  undefined (`attr_no`) on the local.  We don't do anything about
  other inherited attributes, relying on Silver's MWDA, carried out
  prior to evaluation, to ensure it doesn't matter what value they
  have.  We might be able to make them null ourselves by building an
  extensible relation which requires all inherited attributes from
  further extensions to be null.  Something like `ext_E1_inhs_null`
  requires all the inherited attributes from `E1` to be undefined,
  then `others_null_E2` is a relation which combines all the nulling
  relations from other extensions, so all the inheriteds we don't know
  about end up undefined too, if we add this to the equation relations
  for locals.

