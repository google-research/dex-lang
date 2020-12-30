;; Copyright 2019 Google LLC
;;
;; Use of this source code is governed by a BSD-style
;; license that can be found in the LICENSE file or at
;; https://developers.google.com/open-source/licenses/bsd

(setq dex-highlights
  '(("^--.*$"                . font-lock-comment-face)
    ("^> .*$"                . font-lock-comment-face)
    ("^'\\(.\\|\n.\\)*\n\n"  . font-lock-comment-face)
    ("\\w+:"                 . font-lock-comment-face)
    ("^:\\w*"                . font-lock-preprocessor-face)
    ("\\bdef\\b\\|\\bfor\\b\\|\\brof\\b\\|\\bcase\\b\\|\\bdata\\b\\|\\bwhere\\b\\|\\bof\\b\\|\\bif\\b\\|\\bthen\\b\\|\\belse\\b\\|\\binterface\\b\\|\\binstance\\b\\|\\bdo\\b\\|\\bview\\b" .
           font-lock-keyword-face)
    ("--o"                               . font-lock-variable-name-face)
    ("[-.,!$^&*:~+/=<>|?\\\\]"           . font-lock-variable-name-face)
    ("\\b[[:upper:]][[:alnum:]]*\\b"     . font-lock-type-face)
    ("^@[[:alnum:]]*\\b"     . font-lock-keyword-face)
    ))

(defun dex-font-lock-extend-region ()
  (save-excursion
    (goto-char font-lock-beg)
    (re-search-backward "\n\n" nil t)
    (setq font-lock-beg (point))
    (goto-char font-lock-end)
    (re-search-forward "\n\n" nil t)
    (setq font-lock-end (point))))

(define-derived-mode dex-mode fundamental-mode "dex"
  (setq font-lock-defaults '(dex-highlights))
  (setq-local comment-start "--")
  (setq-local comment-end "")
  (setq-local syntax-propertize-function
              (syntax-propertize-rules (".>\\( +\\)" (1 "."))))
  (set (make-local-variable 'font-lock-multiline) t)
  (add-hook 'font-lock-extend-region-functions
            'dex-font-lock-extend-region))

(add-to-list 'auto-mode-alist '("\\.dx\\'"  . dex-mode))
