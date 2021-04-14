

## common
This grammar holds the nonterminal types which are common in
translating commands to Abella and translating output which comes back
from Abella.  By sharing these, the output from Abella can be used to
inform translations of commands going to Abella.


## toAbella
This grammar translates from the proof syntax which uses attribute
grammars to the proof syntax of plain Abella.  This translation
assumes a particular encoding of attribute grammars is used for the
definition.


## fromAbella
This grammar translates Abella's output back to the attribute grammar
syntax used in the proof.  This hides the details of the encoding used
for attribute grammars.


## composed
This grammar brings together translation of commands to send to Abella
and translation of Abella's output in a REPL for an interactive
theorem prover.


## docs
This directory holds documentation about the interface.


## silverabella-PG
This directory holds the Proof General instance for the interface.  To
use it, its files need to be copied to a directory named
`silverabella` in the Proof General directory and the location of the
jar file needs to be changed to reflect your personal set-up.

