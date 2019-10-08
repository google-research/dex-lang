;; Copyright 2019 Google LLC
;;
;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at
;;
;;     https://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.

(setq dex-highlights
  '(("^--.*$"                . font-lock-comment-face)
    ("> .*$"                 . font-lock-comment-face)
    ("^'\\(.\\|\n.\\)*\n\n"  . font-lock-comment-face)
    ("\\blam\\b\\|\\bfor\\b\\|\\btype\\b\\|\\bunpack\\b\\|\\bpack\\b\\|\\btodo\\b"
     . font-lock-keyword-face)
    ("\\bE\\b\\|\\bA\\b"              . font-lock-keyword-face)
    ("->\\|=>\\|\\.\\|@\\|,\\|\\$\\|=\\|;\\|::" . font-lock-variable-name-face)
    ("\\b[[:upper:]][[:alnum:]]*\\b"  . font-lock-type-face)
    (":t\\|:passes\\|:p\\|:time"      . font-lock-preprocessor-face)
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
