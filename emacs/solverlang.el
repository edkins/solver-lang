;;; Based on https://www.emacswiki.org/emacs/ModeTutorial
;;; and https://www.emacswiki.org/emacs/SampleMode

(setq solverlang-doing-highlighting nil)

(defun highlight-based-on-line (line)
  (let ((words (split-string line)))
    (let ((cmd (nth 0 words))
	  (start (string-to-number (nth 1 words)))
	  (end (string-to-number (nth 2 words)))
	  (status (nth 3 words)))
      (if (equal cmd "range")
	  (if (equal status "ok")
	      (set-text-properties start end '(font-lock-face success))
	    (set-text-properties start end '(font-lock-face error)))
	(error "Unexpected cmd received from python")))))

(defun solverlang-remove-highlighting-hook (begin end)
  (if (not solverlang-doing-highlighting)
      (solverlang-actually-remove-highlighting)))

(defun solverlang-actually-remove-highlighting ()
      (set-text-properties (point-min) (point-max) nil))

(defun verify-up-to-point ()
  (interactive)
  (let ((tempfile (make-temp-file "solverlang-input-"))
	(position
	 (if (looking-at "$")
	     (point)
	   (save-excursion (beginning-of-line) (point)))))
    (write-region 1 position tempfile)
    (let ((lines (process-lines "python" (concat load-file-name "../thin/emacs-mode.py") tempfile)))
      (solverlang-actually-remove-highlighting)
      (setq solverlang-doing-highlighting t)
      (dolist (line lines)
	(highlight-based-on-line line))
      (setq solverlang-doing-highlighting nil)
      (delete-file tempfile))))

;;; Keymap
(setq solverlang-mode-map
      (let ((mm (make-sparse-keymap)))
	(define-key mm (kbd "C-c C-<return>") 'verify-up-to-point)
	mm))

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
  (use-local-map solverlang-mode-map)
  (setq-local font-lock-defaults '(solverlang-font-lock-keywords))
  (setq-local indent-line-function 'solverlang-indent-line)
  (setq-local comment-start "# ")
  (setq-local left-margin-width 2)
  (add-hook 'before-change-functions 'solverlang-remove-highlighting-hook))

; Associate mode with .sl files
(add-to-list 'auto-mode-alist '("\\.sl\\'" . solverlang-mode))
