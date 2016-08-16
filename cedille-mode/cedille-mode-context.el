; Welcome to the Cedille Mode Context tool!
; This file contains the code that governs the feature allowing the user to retrieve the context at a given point.


					; GLOBAL DEFINITIONS

(load-library "cedille-mode-info")
(defvar cedille-mode-context-ordering nil)
(defvar cedille-mode-context-filtering nil)

(defvar cedille-mode-original-context-list)
(defvar cedille-mode-filtered-context-list)
(defvar cedille-mode-sorted-context-list)

;;; There are three context lists:
;;; 1. The original list (original)
;;; 2. The list after it has been filtered
;;; 3. The list after it has been sorted
;;; This is also the order in which these lists are processed.
;;; First, the original list is derived using cedille-mode-compute-context()
;;; Second, the filtered list is derived using cedille-mode-filter-context()
;;; Finally, the sorted list is derived using cedille-mode-sort-context()
;;; The sorted list is the one displayed to the user.


					; MINOR MODE FUNCTIONS

(defmacro make-cedille-mode-context-order(arg)
  (` (lambda ()
       (interactive)
       (setq cedille-mode-context-ordering ,arg)
       (other-window 1)
       (cedille-mode-update-buffers)
       (other-window -1))))

(define-minor-mode cedille-context-view-mode
  "Creates context mode, which displays the context of the selected node"
  nil         ; init-value, whether the mode is on automatically after definition
  " Context"  ; indicator for mode line
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "a") (make-cedille-mode-context-order 'fwd)) ; a-z ordering
    (define-key map (kbd "z") (make-cedille-mode-context-order 'bkd)) ; z-a ordering
    (define-key map (kbd "d") (make-cedille-mode-context-order nil)) ; default ordering
    (define-key map (kbd "C") #'cedille-mode-close-context-window) ; exit context mode
    (define-key map (kbd "c") #'cedille-mode-close-context-window) ; exit context mode
    (define-key map (kbd "h") (make-cedille-mode-info-display-page "context mode")) ;help page
    map
    )
  )

(defun cedille-mode-close-context-window() (interactive) (delete-window))

(defun cedille-mode-sort-context()
  "Sorts context according to ordering and stores in cedille-mode-sorted-context-list"
  (let* ((context (copy-sequence cedille-mode-original-context-list))
	 (terms (cond ((equal cedille-mode-context-ordering 'fwd)
		       (sort (car context) (lambda (a b) (string< (car a) (car b)))))		       
		      ((equal cedille-mode-context-ordering 'bkd)
		       (sort (car context) (lambda (a b) (string< (car b) (car a)))))
		      (t (car context))))
	 (types (cond ((equal cedille-mode-context-ordering 'fwd)
		       (sort (cdr context) (lambda (a b) (string< (car a) (car b)))))		       
		      ((equal cedille-mode-context-ordering 'bkd)
		       (sort (cdr context) (lambda (a b) (string< (car b) (car a)))))
		      (t (cdr context)))))
    (setq cedille-mode-sorted-context-list (cons terms types))))

					; FUNCTIONS TO COMPUTE THE CONTEXT

(defun cedille-mode-compute-context()
  "Compute the context and store it in local variables"
  (if se-mode-selected
      ;;Retrieve context from parse tree
      (let ((b (cedille-mode-context-buffer))
	    (p (se-find-point-path (point) (se-mode-parse-tree))))
	;;Store the unmodified context
	(setq cedille-mode-original-context-list (cedille-mode-get-context p)))))

(defun cedille-mode-get-context(path) ; -> list <context>
  "Searches the input path for binder nodes, returning a tuple consisting of:\n
1. A list of term symbols and their types and keywords\n
2. A list of type symbols and their kinds and keywords\n
The output is a tuple (terms types)\n
where each object is a tuple (symbol alist)\n
where alist is an association list containing the info associated with symbol\n
which currently consists of:\n
+ 'value' : the type or kind of symbol
+ 'keywords': a list of keywords associated with symbol"
  (let (terms types)
    (dolist (node path (when (or terms types) (cons terms types)))
      (let ((binder (cdr (assoc 'binder (se-term-data node))))
	    (children (se-node-children node)))
	(when (and binder children)
	  (let* ((bound (string-to-number binder)) ;included for readability
		 (data (se-term-data (nth bound children)))
		 (symbol (cdr (assoc 'symbol data)))
		 (type (cdr (assoc 'type data)))
		 (kind (cdr (assoc 'kind data)))
		 (keywords-string (cdr (assoc 'keywords data))) ;included for readability
		 (keywords-list (list (split-string keywords-string " " t))))
	    (when (and symbol (not (equal symbol "_")) (or type kind))
	      (if type
		  (setq terms (cons (cons symbol (acons 'value type `(keywords . ,keywords-list))) terms))
		(setq types (cons (cons symbol (acons 'value kind `(keywords . ,keywords-list))) types))))))))))

					; FUNCTIONS TO DISPLAY THE CONTEXT

(defun cedille-mode-display-context()
  "Displays the context"
  (let ((b (cedille-mode-context-buffer)))
    (cedille-mode-sort-context)
    (with-current-buffer b
      (setq buffer-read-only nil)
      (erase-buffer)
      (insert (cedille-mode-format-context cedille-mode-sorted-context-list))
      (goto-char 1)
      (fit-window-to-buffer (get-buffer-window b))
      (setq buffer-read-only t)
      (setq deactivate-mark nil))))

(defun cedille-mode-format-context(context) ; -> string
  "Formats the context as text for display"
  (let ((output) ;""
	(format (lambda (pair) (concat (car pair) ":\t" (cdr (assoc 'value (cdr pair))))))
	(terms (car context))
	(types (cdr context)))
    (if (or terms types)
	(progn
	  (when terms ;Print out the terms and their types
	    (setq output (concat "==== TERMS ====\n" (mapconcat format terms "\n") (when types "\n\n"))))
	  (when types ;Print out the types and their kinds
	    (setq output (concat output "==== TYPES ====\n" (mapconcat format types "\n"))))
	  output)
      "Selected context is empty.")))

					; CONVENIENT FUNCTIONS

(defun cedille-mode-context()
  (cedille-mode-compute-context)
  (cedille-mode-display-context)
  (cedille-mode-rebalance-windows))

(defun cedille-mode-context-buffer-name() (concat "*cedille-context-" (file-name-base (buffer-name)) "*"))

(defun cedille-mode-context-buffer() "Retrieves the context buffer" (get-buffer-create (cedille-mode-context-buffer-name)))

(defun cedille-mode-context-window()
  "Retrieves (or creates) the context window"
  (let* ((context-buffer (cedille-mode-context-buffer))
	 (context-window (get-buffer-window context-buffer)))
    (if context-window
	context-window
      (split-window))))

(provide 'cedille-mode-context)
