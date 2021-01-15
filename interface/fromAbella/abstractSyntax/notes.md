
Things to do:
* Pretty printing:
  - I am not trying to split long lines.  I should be.
* I need to hide WPD assumptions.
* I need to add error messages (e.g. syntax error) to `FullDisplay`.
* Check what happens when settings get changed.
* Check what happens with an invalid setting name or value.

* The name `nil` should be acceptable in some places with an
  identifier (e.g. error messages).  This is also true for `toAbella`
  (e.g. theorem names, hypothesis names).  Regular identifiers may not
  use capital letters to start, which is a way to handle this.

