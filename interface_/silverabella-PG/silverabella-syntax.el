
(provide 'silverabella-syntax)


;;I wanted to use a function to join the words together rather than
;;put the full string of them in like this, but Emacs didn't approve
;;of that plan, claiming it was an "invalid function" each time, even
;;though I could run it in *scratch* with the same arguments.  It
;;won't even accept "concat".

(defconst silverabella-top-commands
  '(
    ;;The actual top commands
    ;; Theorem | Define | Import | Kind | Split | Type | Extensible_Theorem
    ("\\(Theorem\\)\\|\\(Define\\)\\|\\(Import\\)\\|\\(Kind\\)\\|\\(Split\\)\\|\\(Type\\)\\|\\(Extensible_Theorem\\)"
     . font-lock-keyword-face)
    ;;Auxiliary words to go with them
    ;; as | by
    ("\\(as\\)\\|\\(by\\)"
     . font-lock-keyword-face)
    ;;Highlighting types
    ("type"
     . font-lock-type-face)
    )
  )
(defconst silverabella-common-commands
  '(
    ;; Set | Show
    ("\\(Set\\)\\|\\(Show\\)"
     . font-lock-keyword-face)
    ;;We want this to stand out, since it doesn't belong in scripts
    ("Quit"
     . font-lock-warning-face)
    )
  )
(defconst silverabella-proof-commands
  '(
    ;;The actual proof commands (minus exists)
    ;; apply | assert | backchain | case | clear | induction | intros | left |
    ;; rename | right | search | split | split* | unfold |
    ;; witness | extensible_induction
    ("\\(apply\\)\\|\\(assert\\)\\|\\(backchain\\)\\|\\(case\\)\\|\\(clear\\)\\|\\(induction\\)\\|\\(intros\\)\\|\\(left\\)\\|\\(rename\\)\\|\\(right\\)\\|\\(search\\)\\|\\(split\\)\\|\\(split*\\)\\|\\(unfold\\)\\|\\(witness\\)\\|\\(extensible_induction\\)"
     . font-lock-function-name-face)
    ;;Auxiliary words to go with them
    ;; keep | on | to
    ("\\(keep\\)\\|\\(on\\)\\|\\(to\\)"
     . font-lock-function-name-face)
    ;;Commands which we don't want to have appear
    ;; skip | abort | #back | #reset | undo
    ("\\(skip\\)\\|\\(abort\\)\\|\\(#back\\)\\|\\(#reset\\)\\|\\(undo\\)"
     . font-lock-warning-face)
    )
  )
(defconst silverabella-comments
  '(
    ;;Line comments
    ("%.*"
     . font-lock-comment-face)
    )
  )

(defconst silverabella-logic
  '(
    ;; forall | exists | nabla
    ("\\(forall\\)\\|\\(exists\\)\\|\\(nabla\\)"
     ;;This needs to use font-lock-keyword-face beacuse 'exists' is in
     ;;both this and proof commands
     . font-lock-keyword-face)
    ;; true | false
    ("\\(true\\)\\|\\(false\\)"
     . font-lock-builtin-face)
    )
  )

(defconst silverabella-output
  '(
    ;;Good proof done
    ("Proof completed."
     ;;There doesn't appear to be any default "success" face, but I'd
     ;;like this to stand out anyway.
     . font-lock-string-face)
    ;;Messages for subgoals completed
    ("\\(completed\\)\\|\\(automatically\\)"
     . font-lock-string-face)
    ;;Bad proof done
    ("Proof ABORTED."
     . font-lock-warning-face)
    ;;Errors in the output
    ;; Error: | Syntax error. | Search failed | Warning:
    ("\\(Error:\\)\\|\\(Syntax error.\\)\\|\\(Search failed\\)\\|\\(Warning:\\)"
     . font-lock-warning-face)
    ;;Highlight debug output prefix to separate it from the actual output
    ("Command sent:"
     . font-lock-string-face)
    )
  )

(defconst silverabella-proof-state
  '(
    ;; Variables:
    ("Variables:"
     . font-lock-keyword-face)
    ;; Subgoal | is: | other subgoals | other subgoal
    ("\\(Subgoal\\)\\|\\(is:\\)\\|\\(other subgoals\\)\\|\\(other subgoal\\)"
     . font-lock-keyword-face)
    ;; Theorem
    ("Theorem"
     . font-lock-keyword-face)
    ("^[a-zA-Z0-9^=`'?$-_]+ : "
     . font-lock-type-face)
    )
  )




(defconst silverabella-script-font-lock-keywords
  (append silverabella-proof-commands
          silverabella-top-commands
          silverabella-common-commands
          silverabella-logic
          silverabella-comments))

(defconst silverabella-goals-font-lock-keywords
  (append silverabella-logic
          silverabella-proof-state))

(defconst silverabella-response-font-lock-keywords
  (append silverabella-logic
          silverabella-output
          silverabella-proof-state))



(defconst silverabella-mode-syntax-table-entries
  (append
   ;;multi-line nested comments
   '(?/ ". 14n")
   '(?* ". 23n")
   ;;single-line comments
   '(?%  "< b")
   '(?\n "> b"))
  )

