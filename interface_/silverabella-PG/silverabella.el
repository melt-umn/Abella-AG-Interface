
(require 'proof)
(require 'proof-easy-config)
(require 'silverabella-syntax)


(define-derived-mode silverabella-shell-mode proof-shell-mode
   "SilverAbella shell" nil
   (silverabella-shell-config)
   (proof-shell-config-done))

(define-derived-mode silverabella-proof-mode proof-mode
   "SilverAbella proof" nil
   (silverabella-proof-config)
   (proof-config-done))

(define-derived-mode silverabella-response-mode proof-response-mode
   "SilverAbella response" nil
   (silverabella-response-config)
   (proof-response-config-done))

(define-derived-mode silverabella-goals-mode proof-goals-mode
   "SilverAbella goals" nil
   (silverabella-goals-config)
   (proof-goals-config-done))


(proof-easy-config
 'silverabella "SilverAbella"
 proof-assistant-home-page  "https://github.com/melt-umn/Abella-AG-Interface"

 proof-prog-name  "java -jar /home/tux/research/Abella-AG-Interface/interface_/composed/interface_.composed.jar"

 proof-context-command                proof-no-regexp
 proof-showproof-command              "Show $$current."
 proof-find-theorems-command          "Show %s."
 proof-save-command-regexp            proof-no-regexp

 ;;Commands end with (period-space) or (period-EOF) or (period-close paren)
 proof-script-command-end-regexp    "\\.\\([ \n\t\r)]\\|$\\)"
 proof-script-comment-start-regexp  "%"
 proof-script-fly-past-comments     t
 proof-script-comment-end           "\n"
 proof-shell-strip-crs-from-input   nil

 proof-undo-n-times-cmd           'silverabella-undo-n
 proof-non-undoables-regexp       "\\(#back\\)\\|\\(#reset\\)\\|\\(undo\\)"
 proof-ignore-for-undo-count      ""
 proof-no-fully-processed-buffer  t
 proof-find-and-forget-fn         'silverabella-find-and-forget-fn

 proof-shell-restart-cmd   "#reset."
 proof-shell-quit-command  "Quit."

 proof-shell-annotated-prompt-regexp  "^.*< $"
 ;;error message regexp taken from Abella PG mode (https://github.com/abella-prover/PG)
 proof-shell-error-regexp            "Error:.*\\|\\(Syntax\\|Typing\\|Unification\\|Unknown\\) error\."
 proof-shell-proof-completed-regexp  "Proof completed."
 ;;This is not working to clear goals, even though it should match
 ;;proof-shell-clear-goals-regexp      "Proof \\(completed\\)\\|\\(aborted\\)."
 ;;This will always match the line, rather than taking the earlier choices
 ;;proof-shell-start-goals-regexp      "\\(Variables:\\)\\|\\([a-zA-Z0-9]+ : \\)\\|\\(=+\n\\)"

 pg-top-term-regexp  "[a-zA-Z0-9^=`'?$-_]+ : "

 proof-script-font-lock-keywords      silverabella-script-font-lock-keywords
 proof-goals-font-lock-keywords       silverabella-goals-font-lock-keywords
 proof-response-font-lock-keywords    silverabella-response-font-lock-keywords
 proof-script-syntax-table-entries    silverabella-mode-syntax-table-entries
 proof-response-syntax-table-entries  silverabella-mode-syntax-table-entries
 proof-goals-syntax-table-entries     silverabella-mode-syntax-table-entries
)

(provide 'silverabella)


;;generate n commands to move back in the proof
(defun silverabella-undo-n (n)
  (if (= n 0)
      nil
    ("#back." . (silverabella-undo-n (- n 1)))
    )
  )


;;These three functions are taken from the Abella PG mode (https://github.com/abella-prover/PG).
;;The names are changed to be appropriate for this PG instance.
(defun silverabella-count (span)
  (setq next (next-span span 'name))
  (if (eq next nil)
    1
    (+ 1 (silverabella-count next))))

(defun silverabella-find-and-forget-cmd (span)
  (setq cmd (span-property span 'cmd))
  (cond
    ((eq cmd nil) "") ; comment
    (t " #back."))
  )

(defun silverabella-find-and-forget-fn (span)
  (setq ans ())
  (while span
    (setq typ (span-property span 'type))
    (if (not (eq typ 'comment))
      (let ((current-cmd (silverabella-find-and-forget-cmd span)))
        (setq ans (cons current-cmd ans))))
    (setq span (next-span span 'type)))
  ans)



;;This is probably not the best way to make it stop messing with the indentation.
;;However, it is the only one which has worked.
;;This makes it start a new line with the same indentation as the previous line
;;   and not change indentation on new line.
(add-hook 'silverabella-mode-hook
          (lambda ()
            (setq-local indent-line-function #'indent-relative)))

