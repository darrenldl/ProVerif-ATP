;;
;; mode for .pi files 
;;

(defvar proverif-pi-kw '("among" "and" "can" "choice" "diff" "clauses" "data" "elimtrue" "else" "equation" "event" "fail" "free" "fun" "if" "in" "let" "new" "noninterf" "not" "nounif" "otherwise" "out" "param" "phase" "putbegin" "pred" "private" "process" "query" "reduc" "suchthat" "sync" "then" "weaksecret" "where") "ProVerif keywords")

(defvar proverif-pi-builtin '("memberOptim" "decompData" "decompDataSelect" "block" "attacker" "mess" "ev" "evinj") "ProVerif builtins")

(defvar proverif-pi-kw-regexp (regexp-opt proverif-pi-kw 'words))
(defvar proverif-pi-builtin-regexp (regexp-opt proverif-pi-builtin 'words))

(defvar proverif-pi-connectives-regexp "\|\\|&\\|->\\|<->\\|<=>\\|==>\\|!")

(setq proverif-piKeywords
 `((,proverif-pi-kw-regexp . font-lock-keyword-face)
   (,proverif-pi-builtin-regexp . font-lock-builtin-face)
   (,proverif-pi-connectives-regexp . font-lock-reference-face)
  )
)

(define-derived-mode proverif-pi-mode fundamental-mode
  (setq font-lock-defaults '(proverif-piKeywords))
  (setq mode-name "ProVerif Pi")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" proverif-pi-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" proverif-pi-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" proverif-pi-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" proverif-pi-mode-syntax-table)
  (modify-syntax-entry ?' "w" proverif-pi-mode-syntax-table)
)

;;
;; mode for .pv files (typed pi calculus)
;;

(defvar proverif-pv-kw '("among" "channel" "choice" "clauses" "const" "def" "diff" "do" "elimtrue" "else" "equation" "equivalence" "event" "expand" "fail" "forall" "foreach" "free" "fun" "get" "if" "implementation" "in" "inj-event" "insert" "let" "letfun" "new" "noninterf" "not" "nounif" "or" "otherwise" "out" "param" "phase" "pred" "proba" "process" "proof" "public_vars" "putbegin" "query" "reduc" "secret" "set" "suchthat" "sync" "table" "then" "type" "weaksecret" "yield") "ProVerif keywords")

(defvar proverif-pv-builtin '("private" "data" "typeConverter" "reachability" "pv_reachability" "real_or_random" "pv_real_or_random" "memberOptim" "decompData" "decompDataSelect" "block" "attacker" "mess") "ProVerif builtins")

(defvar proverif-pv-kw-regexp (regexp-opt proverif-pv-kw 'words))
(defvar proverif-pv-builtin-regexp (regexp-opt proverif-pv-builtin 'words))

(defvar proverif-pv-connectives-regexp "\|\|\\|&&\\|->\\|<->\\|<=>\\|<-R\\|<-\\|==>\\|<=\\|!")

(setq proverif-pvKeywords
 `((,proverif-pv-kw-regexp . font-lock-keyword-face)
   (,proverif-pv-builtin-regexp . font-lock-builtin-face)
   (,proverif-pv-connectives-regexp . font-lock-reference-face)
  )
)

(define-derived-mode proverif-pv-mode fundamental-mode
  (setq font-lock-defaults '(proverif-pvKeywords))
  (setq mode-name "ProVerif Typed Pi")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" proverif-pv-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" proverif-pv-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" proverif-pv-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" proverif-pv-mode-syntax-table)
  (modify-syntax-entry ?' "w" proverif-pv-mode-syntax-table)
)

;;
;; mode for .horn files 
;;

(defvar proverif-horn-kw '("data" "elimtrue" "equation" "fun" "not" "nounif" "param" "pred" "query" "reduc") "ProVerif keywords")

(defvar proverif-horn-builtin '("elimVar" "elimVarStrict" "memberOptim" "decompData" "decompDataSelect" "block") "ProVerif builtins")

(defvar proverif-horn-kw-regexp (regexp-opt proverif-horn-kw 'words))
(defvar proverif-horn-builtin-regexp (regexp-opt proverif-horn-builtin 'words))

(defvar proverif-horn-connectives-regexp "&\\|->\\|<->\\|<=>")

(setq proverif-hornKeywords
 `((,proverif-horn-kw-regexp . font-lock-keyword-face)
   (,proverif-horn-builtin-regexp . font-lock-builtin-face)
   (,proverif-horn-connectives-regexp . font-lock-reference-face)
  )
)

(define-derived-mode proverif-horn-mode fundamental-mode
  (setq font-lock-defaults '(proverif-hornKeywords))
  (setq mode-name "ProVerif Horn")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" proverif-horn-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" proverif-horn-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" proverif-horn-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" proverif-horn-mode-syntax-table)
  (modify-syntax-entry ?' "w" proverif-horn-mode-syntax-table)
)

;;
;; mode for .horntype files 
;;

(defvar proverif-horntype-kw '("type" "name" "const" "forall" "elimtrue" "equation" "fun" "not" "nounif" "set" "pred" "query" "clauses") "ProVerif keywords")

(defvar proverif-horntype-builtin '("elimVar" "elimVarStrict" "memberOptim" "decompData" "decompDataSelect" "block") "ProVerif builtins")

(defvar proverif-horntype-kw-regexp (regexp-opt proverif-horntype-kw 'words))
(defvar proverif-horntype-builtin-regexp (regexp-opt proverif-horntype-builtin 'words))


(setq proverif-horntypeKeywords
 `((,proverif-horntype-kw-regexp . font-lock-keyword-face)
   (,proverif-horntype-builtin-regexp . font-lock-builtin-face)
   (,proverif-horn-connectives-regexp . font-lock-reference-face)
  )
)

(define-derived-mode proverif-horntype-mode fundamental-mode
  (setq font-lock-defaults '(proverif-horntypeKeywords))
  (setq mode-name "ProVerif Typed Horn")

;; comment highlighting
  (modify-syntax-entry ?\( "()1" proverif-horntype-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4" proverif-horntype-mode-syntax-table)
  (modify-syntax-entry ?* ". 23" proverif-horntype-mode-syntax-table)

;; _ and ' belong to ordinary identifiers
  (modify-syntax-entry ?_ "w" proverif-horntype-mode-syntax-table)
  (modify-syntax-entry ?' "w" proverif-horntype-mode-syntax-table)

)
