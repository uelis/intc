
(setq int-keywords
      '("let" "val" "return" "case" "direct" "fn" "if" "then" "else"
        "type" "copy" "in" "of" "as"))

(setq int-types
      '("void" "unit" "bool" "int" "array" "box"))

(setq int-builtin
      '("print" "intadd" "intsub" "intmul" "intdiv" "inteq" "intshl" "intshr" "intsar"
        "intand" "intor" "intxor" "intlt" "intslt" "alloc" "free" "load" "store" "arrayalloc"
        "arrayfree" "arrayget" "push" "pop" "call" "encode" "decode"))
        
(setq int-constants
      '("Inl" "Inr" "True" "False"))

(setq int-keywords-regexp (regexp-opt int-keywords 'words))
(setq int-types-regexp (concat (regexp-opt int-types 'words)
                               "\\|''?'?[[:alnum:]]+"
                               ))
(setq int-constants-regexp (concat (regexp-opt int-constants 'words)
                                   "\\|[A-Z][[:alnum:]]+"))
(setq int-builtin-regexp (regexp-opt int-builtin 'words))

(setq intKeywords
      `(
        ("\"\\.\\*\\?" . font-lock-string-face)
        (,int-constants-regexp . font-lock-constant-face)
        (,int-builtin-regexp . font-lock-builtin-face)
        (,int-types-regexp . font-lock-type-face)
        (,int-keywords-regexp . font-lock-keyword-face)        
        ("(\\|)\\|{\\|}\\|\\\\\\|\\[\\|\\]\\|<\\|>\\|λ\\|+\\|-\\|*\\|/\\|->\\|,\\|:\\|;\\|#\\|=" . font-lock-comment-face)
  )
)

(define-derived-mode int-mode fundamental-mode
  (setq font-lock-defaults '(intKeywords))
  (setq mode-name "int")

  (modify-syntax-entry ?/ ". 14" int-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" int-mode-syntax-table)

  (define-key int-mode-map (kbd "C-c C-c") 'compile) 
)
