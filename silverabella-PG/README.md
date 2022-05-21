

## silverabella-PG
This directory holds the Proof General instance for the interface.  To
use it, its files need to be copied to a directory named
`silverabella` in the Proof General directory and the location of the
jar file needs to be changed to reflect your personal set-up.  You
also need to add the following line to the `generic/proof-site.el`
file in the Proof General directory, in the
`proof-assistant-table-default`:
```
(silverabella "SilverAbella" "svthm")
```
so it will know to open interface files using this mode automatically.

