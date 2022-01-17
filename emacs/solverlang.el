;;; Based on https://www.emacswiki.org/emacs/ModeTutorial
;;; and https://www.emacswiki.org/emacs/SampleMode

(make-variable-buffer-local 'solverlang-doing-highlighting)
(setq-default solverlang-doing-highlighting nil)

(defun highlight-based-on-line (line)
  (if (equal line "")
      0
    (let ((words (split-string line)))
      (let ((cmd (nth 0 words))
	    (start (string-to-number (nth 1 words)))
	    (end (string-to-number (nth 2 words)))
	    (status (nth 3 words)))
	(if (equal cmd "range")
	    (if (equal status "ok")
		(progn
		  (set-text-properties (+ 1 start) (+ 1 end) '(font-lock-face success))
	          0)
	      (progn
		(set-text-properties (+ 1 start) (+ 1 end) '(font-lock-face error))
		(goto-char (+ 1 start))
		1))
	  (progn
	    (error "Unexpected cmd received from python")
	    1))))))
	     

(defun solverlang-remove-highlighting-hook (begin end)
  (if (not solverlang-doing-highlighting)
      (solverlang-actually-remove-highlighting)))

(defun solverlang-actually-remove-highlighting ()
      (set-text-properties 1 (+ 1 (buffer-size)) nil))

(defun solverlang-verify-up-to-point ()
  (interactive)
  (let ((position
	 (if (looking-at "$")
	     (point)
	   (save-excursion (beginning-of-line) (point)))))
    (solverlang-verify-up-to position)))

(defun solverlang-verify-entire-buffer ()
  (interactive)
  (solverlang-verify-up-to (+ 1 (buffer-size))))

(defun solverlang-verify-up-to (position)
  (let ((tempfile (make-temp-file "solverlang-input-")))
    (write-region 1 position tempfile)
    (let ((lines (process-lines "python" (concat (file-name-directory (symbol-file 'solverlang-verify-up-to)) "../thin2/emacs_mode.py") tempfile))
	  (error-count 0))
      (solverlang-actually-remove-highlighting)
      (setq solverlang-doing-highlighting t)
      (dolist (line lines)
	(setq error-count (+ error-count (highlight-based-on-line line))))
      (setq solverlang-doing-highlighting nil)
      (delete-file tempfile)
      (message (concat (number-to-string error-count) " error(s) encountered")))))

;;; Keymap
(setq solverlang-mode-map
      (let ((mm (make-sparse-keymap)))
	(define-key mm (kbd "C-c C-<return>") 'solverlang-verify-up-to-point)
	(define-key mm (kbd "C-c C-b") 'solverlang-verify-entire-buffer)
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
	(prev-line-close-brace
	 (save-excursion (forward-line -1) (looking-at ".*}")))
	(current-line-close-brace
	 (save-excursion (move-beginning-of-line nil) (looking-at ".*}"))))
    (let ((adjusted-indent
	   (+ prev-line-indent
	      (if prev-line-open-brace 2 0)
	      (if current-line-close-brace -2 0)
	      (if prev-line-close-brace -2 0))))
      (if (not first-line) (indent-line-to adjusted-indent)))))

;;; Define mode
(define-derived-mode solverlang-mode prog-mode "Solverlang"
  "Major mode for editing Solver Language files"
  (use-local-map solverlang-mode-map)
  (setq-local font-lock-defaults '(solverlang-font-lock-keywords))
  (setq-local indent-line-function 'solverlang-indent-line)
  (setq-local comment-start "# ")
  (setq-local left-margin-width 2)
  (make-local-variable 'before-change-functions)
  (add-hook 'before-change-functions 'solverlang-remove-highlighting-hook))

; Associate mode with .sl files
(add-to-list 'auto-mode-alist '("\\.sl\\'" . solverlang-mode))
