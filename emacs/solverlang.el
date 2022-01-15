; Based on https://www.emacswiki.org/emacs/ModeTutorial

; Initialize vars
(setq solverlang-mode-hook nil)
(setq solverlang-mode-map (make-sparse-keymap))

; Syntax table
(setq solverlang-mode-syntax-table (make-syntax-table))
(modify-syntax-entry ?# "<" solverlang-mode-syntax-table)
(modify-syntax-entry ?\n ">" solverlang-mode-syntax-table)

; Font lock keywords
(setq solverlang-font-lock-keywords-1
  (list
   '("\\<def\\>" . font-lock-keyword-face)))

(setq solverlang-font-lock-keywords-2
  solverlang-font-lock-keywords-1)

(setq solverlang-font-lock-keywords-3
  (append solverlang-font-lock-keywords-2
    (list
     '("\\('\\w*'\\)" . font-lock-variable-name-face))))

(setq solverlang-font-lock-keywords solverlang-font-lock-keywords-3)

; Indentation
(defun solverlang-indent-line ()
  "Indent current line in Solver Language"
  (interactive)
  (if (> (current-column) (current-indentation))
      (save-excursion (indent-line-to 4))
    (indent-line-to 4)))

(defun solverlang-indent-linezzz ()
  "Indent current line in Solver Language"
  (interactive)
  (beginning-of-line)
  (if (bobp)
      (indent-line-to 0)      ; First line is always non-indented
    (let ((not-indented t) cur-indent)
      (if (looking-at "}")    ; If the line we are looking at is the end of a block, then decrease the indentation
	  (progn
	    (save-excursion
	      (forward-line -1)
	      (setq cur-indent (- (current-indentation) default-tab-width)))
	    (if (< cur-indent 0)   ; We can't indent past the left margin
		(setq cur-indent 0)))
	(save-excursion
	  (while not-indented      ; Iterate backwards until we find an indentation hint
	    (forward-line -1)
	    (if (looking-at "}")   ; This hint indicates that we need to indent at the level of the }
		(progn
		  (setq cur-indent (current-indentation))
		  (setq not-indented nil))
	      (if (looking-at "{") ; This hint indicates that we need to indent an extra level
		  (progn
		    (setq cur-indent (+ (current-indentation) default-tab-width))   ; Do the actual indenting
		    (setq not-indented nil))
		(if (bobp)
		    (setq not-indented nil)))))))
	  (if cur-indent
	      (indent-line-to cur-indent)
	    (indent-line-to 0)))))   ; If we didn't see an indentation hint, then allow no indentation
	    

; Define mode
(defun solverlang-mode ()
  "Major mode for editing Solver Language files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table solverlang-mode-syntax-table)
  (use-local-map solverlang-mode-map)
  (set (make-local-variable 'font-lock-defaults) '(solverlang-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'solverlang-indent-line)
  (setq mode-name "Solverlang")
  (setq major-mode 'solverlang-mode)
  (run-hooks 'solverlang-mode-hook))

; Associate mode with .sl files
(add-to-list 'auto-mode-alist '("\\.sl\\'" . solverlang-mode))
