
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

