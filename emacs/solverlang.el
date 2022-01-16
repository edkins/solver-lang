;;; Based on https://www.emacswiki.org/emacs/ModeTutorial
;;; and https://www.emacswiki.org/emacs/

;;; Keymap
(setq solverlang-mode-map (make-sparse-keymap))

;;; Syntax table
(setq solverlang-mode-syntax-table
      (let ((st (make-syntax-table)))
	(modify-syntax-entry ?+ "." st)
	(modify-syntax-entry ?- "." st)
	(modify-syntax-entry ?* "." st)
	(modify-syntax-entry ?/ "." st)
	(modify-syntax-entry ?< "." st)
	(modify-syntax-entry ?> "." st)
	(modify-syntax-entry ?% "." st)
	(modify-syntax-entry ?$ "." st)
	(modify-syntax-entry ?& "." st)
	(modify-syntax-entry ?| "." st)
	st))

;;; Font lock keywords
(setq solverlang-font-lock-keywords
      '(("\\_<\\(def\\|introduce\\)\\_>" . font-lock-keyword-face)
	("\\_<\\(int\\|bool\\)\\_>" . font-lock-type-face)))

;;; Indentation
(defun solverlang-indent-line ()
  "Indent current line in Solver Language"
  (let ((first-line
	 (save-excursion (beginning-of-line) (bobp)))
	(prev-line-indent
	 (save-excursion (forward-line -1) (current-indentation)))
	(prev-line-open-brace
	 (save-excursion (forward-line -1) (looking-at ".*{")))
	(current-line-close-brace
	 (save-excursion (move-beginning-of-line nil) (looking-at ".*}"))))
    (let ((adjusted-indent
	   (+ prev-line-indent (if prev-line-open-brace 2 0) (if current-line-close-brace -2 0))))
    (if (not first-line) (indent-line-to adjusted-indent)))))

;;; Define mode
(define-derived-mode solverlang-mode prog-mode "Solverlang"
  "Major mode for editing Solver Language files"
  (setq-local font-lock-defaults '(solverlang-font-lock-keywords))
  (setq-local indent-line-function 'solverlang-indent-line)
  (setq-local comment-start "# "))

; Associate mode with .sl files
(add-to-list 'auto-mode-alist '("\\.sl\\'" . solverlang-mode))
