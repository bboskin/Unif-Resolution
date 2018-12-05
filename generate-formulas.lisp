; The depth, number of variables, and number of constant symbols appearing in a formula
(defparameter DEFAULT-DEPTH 7)
(defparameter DEFAULT-VARS 7)
(defparameter DEFAULT-CONSTANTS 3)

;; Enumerations to seed formulas

;; symbols
(defparameter variables '(x y z w x1 y1 z1 w1 x1 y2 z2 w2))
(defparameter num-vars (len variables))

(defparameter constants '(c c0 c1 c2 c3 c4 c5 c6))
(defparameter num-constants (len constants))
(defun random-constant ()
  (nth (random num-constants) constants))

(defparameter string-objects (list "hello" "goodbye" "blah" "ACL2s"))
(defparameter num-strings (len string-objects))
(defun random-string ()
  (nth (random num-strings) string-objects))

(defparameter list-objects
  (list ''(1 2) ''() ''(3 4 5 6) ''(e f g)))
(defparameter num-lists (len list-objects))
(defun random-list ()
  (nth (random num-lists) list-objects))

(defparameter symbol-objects '('a 'b 'c 'd 'e 'f 'g))
(defparameter num-syms (len symbol-objects))
(defun random-symbol ()
  (nth (random num-syms) symbol-objects))

(defparameter quoted-objects (append list-objects symbol-objects))
(defparameter num-quote (len quoted-objects))
(defun random-quoted-obj ()
  (nth (random num-quote) quoted-objects))

(defparameter num-nums 14)
(defun random-num () (random num-nums))

(defparameter fn-syms '((+ 2 number) (binary-append 2 list) (* 2 number)
			))
(defparameter num-fn-syms (len fn-syms))
(defun random-fn ()
  (nth (random num-fn-syms) fn-syms))

(defparameter rel-syms '((<= 2 number) (booleanp 1 nil) (natp 1 nil)
			 (equal 2 nil)))
(defparameter num-rel-syms (len rel-syms))
(defun random-rel ()
  (nth (random num-rel-syms) rel-syms))

(defun random-type ()
  (nth (random 4) '(number list symbol)))

;; Other parameters
(defparameter NUM-FORMS 6)
(defparameter NUM-FOR-ARBITRARY-ARITY 6)
(defun NUM-VARS-AT-BINDING ()
  (+ 1 (random 3)))

(defun random-subset (vars n)
  (if (equal n 0) nil
    (let ((v (nth (random (len vars)) vars)))
      (cons v (random-subset (remove v vars) (- n 1))))))

(defun choose-nary-tag (n)
  (cond
   ((equal n 4) 'and)
   ((equal n 5) 'or)
   (t (choose-nary-tag (+ 4 (random 2))))))

(defun decide-arity ()
  (+ 1 (max 0 (- (truncate NUM-FOR-ARBITRARY-ARITY 2) 1))
     (random (truncate NUM-FOR-ARBITRARY-ARITY 2))))

;; creating atomic formulas/terms
(defun get-random-object (type)
  (cond
   ((equal type 'number) (random-num))
   ((equal type 'string) (random-string))
   ((equal type 'list) (random-list))
   ((equal type 'symbol) (random-symbol))))

(defun new-term (type b-vs fn?)
  (let ((type (if type type (random-type)))
	;; object, constant, variable, or function call
	(r (if fn? (random 7) (random 6))))
    (cond
     ((equal r 0) (get-random-object type))
     ((equal r 1) (random-constant))
     ((< r 6) (nth (random (len b-vs)) b-vs))
     (t
      (let* ((f (random-fn))
	     (f-name (car f))
	     (f-arity (cadr f))
	     (f-types (caddr f)))
	`(,f-name . ,(create-terms f-arity f-types b-vs nil)))))))

(defun create-terms (n type b-vs fn?)
  (cond
   ((equal n 0) nil)
   (t (let ((ts (create-terms (- n 1) type b-vs fn?)))
	(cons (new-term type b-vs fn?) ts)))))

(defun create-atomic-formula (bound-vars)
  ;; it can be either a relation, or an = expression
  (if (equal (random 2) 0)
      `(= . ,(create-terms 2 nil bound-vars t))
    (let* ((P (random-rel))
	   (P-name (car P))
	   (P-arity (cadr P))
	   (P-arg-type (caddr P)))
      `(,P-name . ,(create-terms P-arity P-arg-type bound-vars t)))))

;; mutually recursive helper
(defun create-formulas (n depth b-vs)
  (cond
   ((equal n 0) nil)
   (t (cons (create-formula depth b-vs)
	    (create-formulas (- n 1) depth b-vs)))))

(defun create-formula (depth bound-vars)
  (if (equal depth 0) (create-atomic-formula bound-vars)
    ;; Otherwise, we can introduce a connective (6)
    (let ((r (random 6)))
      (cond
       ((equal r 0) `(not ,(create-formula (- depth 1) bound-vars)))
       ((equal r 1) `(implies ,(create-formula (- depth 1) bound-vars)
			   ,(create-formula (- depth 1) bound-vars)))
       ((equal r 2) `(if ,(create-formula (- depth 1) bound-vars)
			 ,(create-formula (- depth 1) bound-vars)
		       ,(create-formula (- depth 1) bound-vars)))
       ((equal r 3) `(iff ,(create-formula (- depth 1) bound-vars)
			  ,(create-formula (- depth 1) bound-vars)))
       (t (let ((tag (choose-nary-tag r)))
	    `(,tag . ,(create-formulas (decide-arity)
				       (- depth 1) bound-vars))))))))



;; function that randomly creates a formula with depth equal to the input
(defun make-random-formula ()
  (let ((var-list (random-subset variables DEFAULT-VARS)))
    (create-formula DEFAULT-DEPTH var-list)))

(defparameter DEFAULT-DEPTH 3)
