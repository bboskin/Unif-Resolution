
#|

 Copyright © 2018 by Pete Manolios 
 CS 4820 Fall 2018. Pete Manolios.

 Homework 7.
 Due: 12/4 (Midnight)

 For this assignment, work in groups of 2-3. Send me exactly one
 solution per team and make sure to follow the submission instructions
 on the course Web page. In particular, make sure that the subject of
 your email submission is "CS 4820 HWK 7".

 The group members are:

 ... (put the names of the group members here)
 
 Use the same ACL2s build from homework 6.
 
|#

(set-ignore-ok t)
(defttag redirect-set-proofs-co)
(set-raw-mode t)

;; Adapted from milawa
;; books/projects/milawa/ACL2/acl2-hacks/io.lisp

(let ((channel 'null-stream))
  (setf (get channel acl2::*open-output-channel-type-key*) :character)
  (setf (get channel acl2::*open-output-channel-key*) (make-broadcast-stream))
  (acl2::set-proofs-co 'null-stream state)
  (acl2::set-standard-co 'null-stream state))

(set-raw-mode nil)

(acl2s-defaults :set verbosity-level 0)
(acl2::set-ld-post-eval-print nil state)
(acl2::set-ld-pre-eval-print nil state)

;; This gets us to raw lisp.
:q

#| 
 The point of the next few forms is that we can use ACL2s from within
 lisp. That will be useful to check that your code works.
|#

(defun acl2s-last-result ()
  (let ((state *the-live-state*))
    (@ result)))
#|

 If c is acl2s computation such as 

 (+ 1 2)
 (append '(1 2) '(3 4))

 etc.

 then the following form will ask ACL2 to evaluate c and will update
 the ACL2 global result to contain a list whose car is a flag
 indicating whether an error occurred, so nil means no error, and whose
 second element is the result of the computation, if no error occurred.

|#

(defun acl2s-compute (c)
  (let ((state *the-live-state*))
    (multiple-value-bind (erp val state)
        (ld `((assign result ,c)))
      (if (equal val :eof)
          (ld `((assign result (list nil (@ result)))))
        (ld `((assign result (list t nil))))))
    (acl2s-last-result)))

#|

Here are some examples

(acl2s-compute '(+ 1 2))
(acl2s-compute '(append '(1 2) '(3 4)))
(acl2s-compute '(+ 1  '(1 2)))

|#


#|

 If q is acl2s query that returns an error-triple such as 

 (pbt 0)
 (test? (equal x x))
 (thm (equal x x))

 etc.

 then the following form will ask ACL2 to evaluate q and will update
 the ACL2 global result to contain a list whose car is a flag
 indicating whether an error occurred, so nil means no error, and whose
 second element is nil.

|#

(defun acl2s-query (q)
  (let ((state *the-live-state*))
    (ld `((mv-let
           (erp val state)
           ,q
           (assign result (list erp nil)))))
    (acl2s-last-result)))

#|

 Here are some examples you can try to see how acl2s-query works.

 (acl2s-query '(pbt 0))
 (acl2s-query '(test? (equal x y)))
 (acl2s-query '(thm (equal x x)))
 (acl2s-query '(thm (iff (implies p q)
                         (or (not p) q))))

|#

#|

 A function that determines if f is a function defined in ACL2s and if
 so, its arity (number of arguments). If f is not a function, then the
 arity is nil. Otherwise, the arity is a natural number. Note that f
 can't be a macro.

|#

(defun acl2s-arity (f)
  (second (acl2s-compute `(arity ',f (w state)))))

#|
 Some examples

 (acl2s-arity 'append)        ; is nil since append is a macro
 (acl2s-arity 'binary-append) ; is 2

|#

#|

 Next, we need to load some software libraries using quicklisp.  For
 example, the trivia library provides pattern matching
 capabilities. Search for "match" below. You can see the online
 documentation for the other software libraries.

|#

(load "~/quicklisp/setup.lisp")
(ql:quickload :trivia)
(ql:quickload :cl-ppcre)
(ql:quickload :let-plus)
(setf ppcre:*allow-named-registers* t)

#|
 
 We now define our own package.

|#

(defpackage :tp (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :tp)

;; We import acl2s-query into our package.

(import '(acl2::acl2s-query acl2::acl2s-arity acl2::acl2s-compute))

#|
 
 We have a list of the propositional operators and information about
 them. 

 :arity can be a positive integer or - (meaning arbitrary arity) If
 :arity is -, there must be an identity and the function must be
 associative and commutative.

 If :identity is non-nil, then the operator has the indicated
 identity. 
 
 An operator is idempotent iff :idem is t.

 If :sink is not -, then it must be the case that (op ... sink ...) =
 sink, e.g., (and ... nil ...) = nil.

 FYI: it is common for global variables to be enclosed in *'s. 

|# 

(defparameter *p-ops*
  '((and     :arity - :identity t   :idem t   :sink nil)
    (or      :arity - :identity nil :idem t   :sink t)
    (not     :arity 1 :identity -   :idem nil :sink -)
    (implies :arity 2 :identity -   :idem nil :sink -)
    (iff     :arity - :identity t   :idem nil :sink -)
    (if      :arity 3 :identity -   :idem nil :sink -)))


#|
mapcar is like map. See the common lisp manual.
In general if you have questions about lisp, ask on Piazza.
|#

(defparameter *p-funs* (mapcar #'car *p-ops*))
(defparameter *fo-quantifiers* '(forall exists))
(defparameter *booleans* '(t nil))
(defparameter *fo-keywords*
  (append *p-funs* *booleans* *fo-quantifiers*))

#|

 See the definition of member in the common lisp manual.  Notice that
 there are different types of equality, including =, eql, eq, equal
 and equals. We need to be careful, so we'll just use equal and we'll
 define functions that are similar to the ACL2s functions we're
 familiar with.

|# 

(defun in (a x)
  (member a x :test #'equal))

(defmacro len (l) `(length ,l))

(defun p-funp (x)
  (in x *p-funs*))

(defun get-alist (k l)
  (cdr (assoc k l :test #'equal)))

(defun get-key (k l)
  (cadr (member k l :test #'equal)))

(defun remove-dups (l)
  (remove-duplicates l :test #'equal))

(defmacro == (x y) `(equal ,x ,y))
(defmacro != (x y) `(not (equal ,x ,y)))

(defun booleanp (x)
  (in x *booleans*))

(defun no-dupsp (l)
  (or (endp l)
      (and (not (in (car l) (cdr l)))
           (no-dupsp (cdr l)))))

(defun pfun-argsp (pop args)
  (and (p-funp pop)
       (let ((arity (get-key :arity (get-alist pop *p-ops*))))
         (and (or (== arity '-)
                  (== (len args) arity))
              (every #'p-formulap args)))))


#|

 Next we have some utilities for converting propositional formulas to
 ACL2 formulas.

|#

(defun to-acl2 (f)
  (match f
    ((type symbol) (intern (symbol-name f) "ACL2"))
    ((cons x xs)
     (mapcar #'to-acl2 f))
    (_ f)))

#|

 A FO term is either a 

 constant symbol: a symbol whose name starts with "C" and is
 optionally followed by a natural number with no leading 0's, e.g., c0,
 c1, c101, c, etc are constant symbols, but c00, c0101, c01, etc are
 not. Notice that (gentemp "C") will create a new constant. Notice
 that symbol names  are case insensitive, so C1 is the same as c1.

 quoted constant: anything of the form (quote object) for any object

 constant object: a rational, boolean, string, character or keyword

 variable: a symbol whose name starts with "X", "Y", "Z", "W", "U" or
 "V" and is optionally followed by a natural number with no leading
 0's (see constant symbol). Notice that (gentemp "X") etc will create
 a new variable.

 function application: (f t1 ... tn), where f is a
 non-constant/non-variable/non-boolean symbol starting with a
 letter (A-Z). The arity of f is n and every occurrence of (f ...)  in
 a term or formula has to have arity n. Also, if f is a defined
 function in ACL2s, its arity has to match what ACL2s expects. We 
 allow functions of 0-arity.
 
|#

(defun char-nat-symbolp (s chars)
  (and (symbolp s)
       (let ((name (symbol-name s)))
         (and (<= 1 (len name))
              (in (char name 0) chars)
              (or (== 1 (len name))
                  (let ((i (parse-integer name :start 1)))
                    (and (integerp i)
                         (<= 0 i)
                         (string= (format nil "~a~a" (char name 0) i)
                                  name))))))))

(defun constant-symbolp (s)
  (char-nat-symbolp s '(#\C)))

(defun variable-symbolp (s)
  (char-nat-symbolp s '(#\X #\Y #\Z #\W #\U #\V)))

(defun quotep (c)
  (and (consp c)
       (== (car c) 'quote)))

(defun constant-objectp (c)
  (typep c '(or boolean rational simple-string standard-char keyword)))

#|

Examples

(constant-objectp #\a)
(constant-objectp 0)
(constant-objectp 1/221)
(constant-objectp "hi there")
(constant-objectp t)
(constant-objectp nil)
(constant-objectp :hi)
(constant-objectp 'a)

(quotep '1)  ; recall that '1 is evaluated first
(quotep ''1) ; but this works
(quotep '(1 2 3))  ; similar to above
(quotep ''(1 2 3)) ; similar to above
(quotep (list 'quote (list 1 2 3))) ; verbose version of previous line

|#

(defun function-symbolp (f)
  (and (symbolp f)
       (not (in f *fo-keywords*))
       (not (keywordp f))
       (not (constant-symbolp f))
       (not (variable-symbolp f))))

#|

(function-symbolp 'c)
(function-symbolp 'c0)
(function-symbolp 'c00)
(function-symbolp 'append)
(function-symbolp '+)

|#

(defmacro mv-and (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a ,b (values nil ,fsig ,rsig)))

(defmacro mv-or (a b &optional (fsig 'fsig) (rsig 'rsig))
  `(if ,a (values t ,fsig ,rsig) ,b))

(defun fo-termp (term &optional (fsig nil) (rsig nil))
  (match term
    ((satisfies constant-symbolp) (values t fsig rsig))
    ((satisfies variable-symbolp) (values t fsig rsig))
    ((satisfies quotep) (values t fsig rsig))
    ((satisfies constant-objectp) (values t fsig rsig))
    ((list* f args)
     (mv-and 
      (and (function-symbolp f) (not (get-alist f rsig)))
      (let* ((fsig-arity (get-alist f fsig))
             (acl2s-arity
              (or fsig-arity
                  (acl2s-arity (to-acl2 f))))
             (arity (or acl2s-arity (len args)))
             (fsig (if fsig-arity fsig (acons f arity fsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))

(defun fo-termsp (terms fsig rsig)
  (mv-or (endp terms)
         (let+ (((&values res fsig rsig)
                 (fo-termp (car terms) fsig rsig)))
               (mv-and res
                       (fo-termsp (cdr terms) fsig rsig)))))


;;;; a faster version of fo-termp that doesn't involve
;;;; connecting with ACL2s
;;;; it ignores signatures, but as long as it is given
;;;; formulas that respect function symbols, it's fine.



#|

Examples

(fo-termp '(f d 2))
(fo-termp '(f c 2))
(fo-termp '(f c0 2))
(fo-termp '(f c00 2))
(fo-termp '(f '1 '2))
(fo-termp '(f (f '1 '2)
              (f v1 c1 '2)))


(fo-termp '(binary-append '1 '2))
(fo-termp '(binary-append '1 '2 '3))
(fo-termp '(binary-+ '1 '2))
(fo-termp '(+ '1 '2)) 
(fo-termp '(- '1 '2))

|#

#|

 A FO atomic formula is either an 

 atomic equality: (= t1 t2), where t1, t2 are FO terms.

 atomic relation: (P t1 ... tn), where P is a
 non-constant/non-variable symbol. The arity of P is n and every
 occurrence of (P ...) has to have arity n. Also, if P is a defined
 function in ACL2s, its arity has to match what ACL2s expects.  We do
 not check that if P is a defined function then it has to return a
 Boolean. Make sure do not use such examples.

|#

(defun relation-symbolp (f)
  (function-symbolp f))

#|

Examples

(relation-symbolp '<)
(relation-symbolp '<=)
(relation-symbolp 'binary-+)

|#

(defun fo-atomic-formulap (f &optional (fsig nil) (rsig nil))
  (match f
    ((list '= t1 t2)
     (fo-termsp (list t1 t2) fsig rsig))
    ((list* r args)
     (mv-and 
      (and (relation-symbolp r) (not (get-alist r fsig)))
      (let* ((rsig-arity (get-alist r rsig))
             (acl2s-arity
              (or rsig-arity
                  (acl2::acl2s-arity (to-acl2 r))))
             (arity (or acl2s-arity (len args)))
             (rsig (if rsig-arity rsig (acons r arity rsig))))
        (mv-and (== arity (len args))
                (fo-termsp args fsig rsig)))))
    (_ (values nil fsig rsig))))


#|
 
 Here is the definition of a propositional formula. We allow
 Booleans.
 
|#

(defun pfun-fo-argsp (pop args fsig rsig)
  (mv-and (p-funp pop)
          (let ((arity (get-key :arity (get-alist pop *p-ops*))))
            (mv-and (or (== arity '-)
                        (== (len args) arity))
                    (fo-formulasp args fsig rsig)))))

(defun p-fo-formulap (f fsig rsig)
  (match f
    ((type boolean) (values t fsig rsig))
    ((list* pop args)
     (if (p-funp pop)
         (pfun-fo-argsp pop args fsig rsig)
       (values nil fsig rsig)))
    (_ (values nil fsig rsig))))

#|
 
 Here is the definition of a quantified formula. 

 The quantified variables can be a variable 
 or a non-empty list of variables with no duplicates.
 Examples include

 (exists w (P w y z x))
 (exists (w) (P w y z x))
 (forall (x y z) (exists w (P w y z x)))

 But this does not work

 (exists c (P w y z x))
 (forall () (exists w (P w y z x)))
 (forall (x y z x) (exists w (P w y z x)))

|#

(defun quant-fo-formulap (f fsig rsig)
  (match f
    ((list q vars body)
     (mv-and (and (in q *fo-quantifiers*)
                  (or (variable-symbolp vars)
                      (and (consp vars)
                           (no-dupsp vars)
                           (every #'variable-symbolp vars))))
             (fo-formulap body fsig rsig)))
    (_ (values nil fsig rsig))))



(defun mv-seq-first-fun (l)
  (if (endp (cdr l))
      (car l)
    (let ((res (gensym))
          (f (gensym))
          (r (gensym)))
      `(multiple-value-bind (,res ,f ,r)
           ,(car l)
         (if ,res
             (values t ,f ,r)
           ,(mv-seq-first-fun (cdr l)))))))

(defmacro mv-seq-first (&rest rst)
  (mv-seq-first-fun rst))
  
(defun fo-formulap (f &optional (fsig nil) (rsig nil))
  (mv-seq-first
   (fo-atomic-formulap f fsig rsig)
   (p-fo-formulap f fsig rsig)
   (quant-fo-formulap f fsig rsig)
   (values nil fsig rsig)))

(defun fo-formulasp (fs fsig rsig)
  (mv-or (endp fs)
         (let+ (((&values res fsig rsig)
                 (fo-formulap (car fs) fsig rsig)))
               (mv-and res
                       (fo-formulasp (cdr fs) fsig rsig)))))



#|

 We can use fo-formulasp to find the function and relation
 symbols in a formula as follows.
 
|#

(defun fo-f-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
        (mapcar #'car fsig)))

(defun fo-r-symbols (f)
  (let+ (((&values res fsig rsig)
          (fo-formulap f)))
        (mapcar #'car rsig)))

#|

Examples

(fo-formulap 
 '(forall (x y z) (exists w (P w y z x))))

(fo-formulap 
 '(forall (x y z x) (exists w (P w y z x))))

(quant-fo-formulap 
 '(forall (x y z) (exists y (P w y z x))) nil nil)

(fo-formulap
 '(exists w (P w y z x)))

(fo-atomic-formulap
 '(exists w (P w y z x)) nil nil)

(quant-fo-formulap 
 '(exists w (P w y z x)) nil nil)

(fo-formulap 
 '(P w y z x))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall (x y z) (or (not (= (q z) (r z))) nil (p '1 x y))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w))))

(fo-formulap
 '(exists w (implies (forall x1 (iff (p1 x1 w) (q c1) (r c2)))
                     (p '2 y w))))

(fo-formulap
 '(and (forall (x y z) (or (not (= (q2 z) (r2 z))) nil (p '1 x y)))
       (exists w (implies (forall x1 (iff (= (p1 x1 w) c2) (q c1) (r c2)))
                          (p '2 y w)))))

(fo-formulap
 '(forall x1 (iff (p1 x1 w) (q c1) (r c2))))

(fo-formulap
 '(iff (p1 x1 w) (q c1) (r c2)))

(fo-atomic-formulap
 '(p1 x1 w))

(fo-atomic-formulap
 '(= (p1 x 3) (p2 c1324 3)))


(variable-symbolp 'c1)
(fo-termp 'x1)
(fo-termp 'w1)
(fo-termp '(x1 w) nil nil)
(fo-termsp '(x1 w) nil nil)

|#

#|
 
 Where appropriate, for the problems below, modify your solutions from
 homework 6. For example, you already implemented most of the
 simplifications in Question 1 in homework 6.
 
|#

#|
 
 Question 1. (25 pts)

 Define function fo-simplify that given a first-order (FO) formula
 returns an equivalent FO formula with the following properties.

 A. The returned formula is either a constant or does not include any
 constants. For example:

 (and (p x) t (q t y) (q y z)) should be simplified to 
 (and (p x) (q t y) (q y z)) 

 (and (p x) t (q t b) nil) should be simplified to nil

 B. Expressions are flattened, e.g.:

 (and (p c) (= c '1) (and (r) (s) (or (r1) (r2)))) is not flat, but this is
 (and (p c) (= c '1) (r) (s) (or (r1) (r2)))

 A formula of the form (op ...) where op is a Boolean operator applied
 to 0 or 1 arguments is not flat. For example, replace (and) with t. A
 formula of the form (op ... (op ...)) where op is a Boolean operator
 is not flat. For example, replace (and p q (and r s)) with (and p q r
 s).

 C. If there is Boolean constant s s.t. If (op ... s ...) = s, then we
 say that s is a sink of op. For example t is a sink of or. A formula
 is sink-free if no such subformulas remain. The returned formula
 should be sink-free.

 D. Simplify your formulas so that no subexpressions of the following
 form remain (where f is a formula)
 
 (not (not f))

 E. Simplify formulas so that no subexpressions of the following form
 remain 

 (op ... p ... q ...)

 where p, q are equal literals or  p = (not q) or q = (not p).

 For example
 
 (or (f) (f1) (p a b) (not (p a b)) (= w z)) should be simplified to 

 t
 
 F. Simplify formulas so there are no vacuous quantified formulas.
 For example, 

 (forall (x w) (P y z))  should be simplified to
 
 (P y z)

 and 

 (forall (x w) (P x y z))  should be simplified to
 
 (forall (x) (P x y z)) 

 G. Simplify formulas by using ACL2s to evaluate, when possible, terms
 of the form (f ...) where f is an ACL2s function all of whose
 arguments are either constant-objects or quoted objects.

 For example,

 (P (binary-+ 4 2) 3)

 should be simplified to

 (P 6 3)

 Hint: use acl2s-compute and to-acl2. For example, consider

 (acl2s-compute (to-acl2 '(binary-+ 4 2)))

 On the other hand,

 (P (binary-+ 'a 2) 3)

 does not get simplified because 
 
 (acl2s-compute (to-acl2 '(binary-+ 'a 2)))

 indicates an error (contract/guard violation). See the definition of
 acl2s-compute to see how to determine if an error occurred.

 H. Test your definitions using at least 10 interesting formulas.  Use
 the acl2s code, if you find it useful.  Include deeply nested
 formulas, all of the Boolean operators, quantified formulas, etc.
|#

(defmacro mv-let (b v e) `(multiple-value-bind ,b ,v ,e))

(defun atomic-formulap (e)
  (mv-let (v f-sig r-sig) (fo-atomic-formulap e) v))
(defun quantified-formulap (e)
  (mv-let (v f-sig r-sig) (quant-fo-formulap e nil nil) v))


;; set/list operations
(defun difference (s1 s2)
  (remove-if-not #'(lambda (e) (not (in e s2))) s1))

(defun set-intersection (s1 s2)
  (remove-if-not #'(lambda (e) (in e s2)) s1))

(defun set-binary-union (s1 s2)
  (append s1 (difference s2 s1)))

(defmacro set-union (&rest s)
  (cond
   ((endp s) nil)
   ((endp (cdr s)) (car s))
   (t `(set-binary-union ,(car s) (set-union . ,(cdr s))))))

(defun snoc (x ls)
  (reduce #'cons ls :initial-value (list x) :from-end t))


;; free and bound variables
(defun free-vars (f)
  (match f
    ((satisfies variable-symbolp) (list f))
    ((list 'forall vars e) (difference (free-vars e) vars))
    ((list 'exists vars e) (difference (free-vars e) vars))
    ((satisfies quotep) nil)
    ((list* op es)
     (reduce #'set-binary-union
	     (mapcar #'free-vars es)
	     :initial-value nil
	     :from-end t))
    (t nil)))

(defun bound-vars (f)
  (match f
    ((satisfies variable-symbolp) nil)
    ((list 'forall vars e) (set-binary-union (free-vars e) vars))
    ((list 'exists vars e) (set-binary-union (free-vars e) vars))
    ((satisfies quotep) nil)
    ((list* op es)
     (reduce #'set-binary-union
	     (mapcar #'bound-vars es)
	     :initial-value nil
	     :from-end t))
    (t nil)))

;; simplifying nary iff
(defun make-binary-iff (es)
  (cond
   ((endp es) t)
   ((endp (cdr es)) (car es))
   (t (let ((p (car es))
	    (q (cadr es))
	    (rst (cddr es)))
	(cond
	 ((equal p q) (make-binary-iff rst))
	 ((endp rst) `(iff ,p ,q))
	 (t `(iff (iff ,p ,q) ,(make-binary-iff rst))))))))

(defun simplify-iff (es)
  (let ((es (mapcar #'fo-simplify es)))
    (make-binary-iff es)))

;; negation of fo formulas
(defun negate (f)
  (match f
    ((satisfies booleanp) (not f))
    ((satisfies atomic-formulap) `(not ,f))
    ((list 'not e) e)
    (f `(not ,f))))

(defun compute-and-decide (f)
  (let ((r (acl2s-compute f)))
    (if (car r) f (cadr r))))

(defun simplify-atomic-formula (f)
  (match f
    ((satisfies quotep) `(quote ,(compute-and-decide f)))
    ((satisfies constant-objectp) (compute-and-decide f))
    ((satisfies symbolp) f)
    ((list '= e1 e2)
     (let ((e1 (simplify-atomic-formula e1))
	   (e2 (simplify-atomic-formula e2)))
       (if (equal e1 e2) t
	 `(= ,e1 ,e2))))
    ((list* op es) (compute-and-decide
		    `(,op . ,(mapcar #'simplify-atomic-formula es))))))

(defun simplify-quantified-formula (f)
  (let ((op (car f))
	(vars (cadr f))
	(e (fo-simplify (caddr f))))
    (let ((e-vs (free-vars e)))
      (let ((vars (intersection vars e-vs)))
	(if vars `(,op ,(reverse vars) ,e) e)))))

(defun flatten (ls ig sink sym seen negs)
  (cond
   ((endp ls)
    (cond
     ((endp seen) sink)
     ((endp (cdr seen)) (car seen))
     (t `(,sym . ,seen))))
   ((== (car ls) ig) (flatten (cdr ls) ig sink sym seen negs))
   ((in (car ls) seen) (flatten (cdr ls) ig sink sym seen negs))
   ((== (car ls) sink) sink)
   ((or (atomic-formulap (car ls))
	(variable-symbolp (car ls))
	(and (consp (car ls)) (equal (caar ls) 'not)))
    (if (in (car ls) negs) sink
      (let ((neg (negate (car ls))))
	(flatten (cdr ls) ig sink sym (snoc (car ls) seen) (cons neg negs)))))
   ((and (consp (car ls)) (equal (caar ls) sym))
    (flatten (append (cdar ls) (cdr ls)) ig sink sym seen negs))
   (t (flatten (cdr ls) ig sink sym (snoc (car ls) seen) negs))))

(defun simplify-and (ls) (flatten ls t nil 'and nil nil))
(defun simplify-or (ls) (flatten  ls nil t 'or nil nil))

(defun simplify-if (test conseq alt)
  (cond
   ((booleanp test) (if test conseq alt))
   ((equal conseq alt) conseq)
   ((booleanp conseq)
    (if conseq `(or ,test ,alt)
      `(and (not ,test) ,alt)))
   ((booleanp alt)
    (if alt `(or (not ,test) ,conseq)
      `(and ,test ,conseq)))
   (t `(if ,test ,conseq ,alt))))

(defun fo-simplify (f)
  (match f
    ;; base cases
    ((satisfies booleanp) f)
    ;; connectives
    ((list 'not e) (negate (fo-simplify e)))
    ((list* 'and es)
     (simplify-and (mapcar #'fo-simplify es)))
    ((list* 'or es)
     (simplify-or (mapcar #'fo-simplify es)))
    ((list 'implies e1 e2)
     (simplify-or `(,(negate (fo-simplify e1)) ,(fo-simplify e2))))
    ((list 'if test conseq alt)
     (let ((test (fo-simplify test))
	   (conseq (fo-simplify conseq))
	   (alt (fo-simplify alt)))
       (simplify-if test conseq alt)))
    ((list* 'iff es) (simplify-iff es))
    ((satisfies atomic-formulap) (simplify-atomic-formula f))
    ((satisfies quantified-formulap) (simplify-quantified-formula f))
    (f (error "Invalid formula ~a" f))))

;; random term generator -- not as easy to use here as it was for hwk6
;; but this lets us perform random testing for quantifier-free formulas

(load "generate-formulas.lisp")

(defun test-fo-simplify (form)
  (print "FORMULA IS:")
  (print form)
  (print "started simplification")
  (let ((form-simp (fo-simplify form)))
    (print "finished simplification")
    (print "simplified form is:")
    (print form-simp)
    (let ((form (to-acl2 form))
	  (form-simp (to-acl2 form-simp)))
      (assert (equal '(nil nil)
		     (acl2s-query
		      `(acl2s::thm (equal ,form ,form-simp))))))))

#|
(loop for i from 1 to 10
      do (let ((f (make-random-formula)))
	   (test-fo-simplify f)))

(test-fo-simplify (make-random-formula))
|#
#|

 Question 2. (10 pts)

 Define nnf, a function that given a FO formula, something that
 satisfies fo-formulap, puts it into negation normal form (NNF).

 The resulting formula cannot contain any of the following
 propositional connectives: implies, iff, if.

 Test nnf using at least 10 interesting formulas. Make sure you
 support quantification.

|#

; no longer used by nnf, but is useful later on
(defun negate* (f)
  (match f
    ((satisfies booleanp) (not f))
    ((satisfies atomic-formulap) `(not ,f))
    ((list 'not f) f)
    ((list 'forall vars f) `(exists ,vars ,(negate* f)))
    ((list 'exists vars f) `(forall ,vars ,(negate* f)))
    ((list* 'and fs) `(or . ,(mapcar #'negate* fs)))
    ((list* 'or fs) `(and . ,(mapcar #'negate* fs)))
    (f (error "Invalid formula ~a" f))))

(defun nnf- (f neg?)
  (match f
    ((satisfies booleanp) (if neg? (not f) f))
    ((satisfies atomic-formulap) (if neg? `(not ,f) f))
    ((list 'not f) (nnf- f (not neg?)))
    ((list 'forall vars f)
     (if neg? `(exists ,vars ,(nnf- f t)) `(forall ,vars ,(nnf- f nil))))
    ((list 'exists vars f)
     (if neg? `(forall ,vars ,(nnf- f t)) `(exists ,vars ,(nnf- f nil))))
    ((list* 'and fs)
     (if neg? `(or . ,(mapcar #'(lambda (e) (nnf- e t)) fs))
       `(and . ,(mapcar #'(lambda (e) (nnf- e nil)) fs))))
    ((list* 'or fs)
     (if neg? `(and . ,(mapcar #'(lambda (e) (nnf- e t)) fs))
       `(or . ,(mapcar #'(lambda (e) (nnf- e nil)) fs))))
    ((list 'implies e1 e2)
     (if neg?
	 `(and ,(nnf- e1 nil) ,(nnf- e2 t))
       `(or ,(nnf- e1 t) ,(nnf- e2 nil))))
    ((list 'iff e1 e2)
     (if neg?
	 `(or (and ,(nnf- e1 nil) ,(nnf- e2 t))
	      (and ,(nnf- e2 nil) ,(nnf- e1 t)))
       `(and (or ,(nnf- e1 t) ,(nnf- e2 nil))
	     (or ,(nnf- e2 t) ,(nnf- e1 nil)))))
    ((list 'if test conseq alt)
     (if neg?
	 `(or (and ,(nnf- test nil) ,(nnf- conseq t))
	      (and ,(nnf- test t) ,(nnf- alt t)))
       `(and (or ,(nnf- test t) ,(nnf- conseq nil))
	     (or ,(nnf- test nil) ,(nnf- alt nil)))))
    (f (error "Invalid formula ~a" f))))

(defun nnf (f)
  (fo-simplify (nnf- f nil)))

;; Testing on quantifier-free formulas
(defun test-nnf (form)
  (print "FORMULA is:")
  (print form)
  (print "started simplification")
  (let ((form-simp (fo-simplify form)))
    (progn (print "finished simplification")
	   (print "started nnf")
	   (let ((form-nnf (nnf form-simp)))
	     (print "finished nnf")
	     (print "NNF form is:")
	     (print form-nnf)
	     (let ((form (to-acl2 form))
		   (form-nnf (to-acl2 form-nnf)))
	       (assert (equal '(nil nil)
			      (acl2s-query
			       `(acl2s::thm (equal ,form ,form-nnf))))))))))

(defparameter DEFAULT-DEPTH 3)

#|
(loop for i from 1 to 10
      do (let ((f (make-random-formula)))
	   (test-nnf f)))
|#
#|

 Question 3. (25 pts)

 Define simp-skolem-pnf-cnf, a function that given a FO formula,
 simplifies it using fo-simplify, then puts it into negation normal
 form, applies skolemization, then puts the formula in prenex normal
 form and finally transforms the matrix into an equivalent CNF
 formula.

 To be clear: The formula returned should be equi-satisfiable with the
 input formula, should contain no existential quantifiers, and if it
 has quantifiers it should be of the form

 (forall (...) matrix)

 where matrix is quantifier-free and in CNF. 

 Test your functions using at least 10 interesting formulas. 

|#
; generating new names predictably

(defparameter SKOLEM-COUNTER 11)
(defparameter PRENEX-COUNTER 11)
(defparameter TSEITIN-COUNTER 11)

(defmacro defnewsymbol (name ctr tag &rest arg)
  (let ((str (if arg `((symbol-name . ,arg) (write-to-string i))
	       `((write-to-string i)))))
    `(defun ,name ,arg
       (let ((i ,ctr))
	 (defparameter ,ctr (+ i 1))
	 (intern (concatenate 'string
			      ,tag
			      . ,str))))))

(defnewsymbol new-fn-symbol SKOLEM-COUNTER "F" e)
(defnewsymbol new-constant-symbol SKOLEM-COUNTER "C")
(defnewsymbol new-rel-symbol TSEITIN-COUNTER "REL")
(defnewsymbol new-variable-symbol PRENEX-COUNTER "" v)

;; Environments are useful throughout
; different kinds of environment extension

(defun extend-env/fns (env xs bvars)
  (append (mapcar #'(lambda (v) (cons v `(,(new-fn-symbol v) . ,bvars))) xs) env))

(defun extend-env/constants (env xs)
  (append (mapcar #'(lambda (v) (cons v (new-constant-symbol))) xs) env))

(defun extend-env/self (env xs)
  (append (mapcar #'(lambda (x) (cons x x)) xs) env))

(defun extend-fresh (vs existing)
  (cond
   ((endp vs) nil)
   (t (cons (if (in (car vs) existing)
		(cons (car vs) (new-variable-symbol (car vs)))
	      (cons (car vs) (car vs)))
	    (extend-fresh (cdr vs) existing)))))

; environment lookup
(defun lookup (y env)
  (cond
   ((endp env) (new-constant-symbol))
   ((equal (caar env) y) (cdar env))
   (t (lookup y (cdr env)))))

;;;;;;;;;;;;;;;;
;; Skolemization

(defun pconnectivep (e) (in e *p-funs*))

(defun skolemize-term (v env)
  (cond
   ((constant-symbolp v) v)
   ((symbolp v) (lookup v env))
   ((and (consp v) (function-symbolp (car v)))
    `(,(car v) . ,(mapcar #'(lambda (e) (skolemize-term e env)) (cdr v))))
   (t v)))

(defun skolemize-atomic-formula (f env)
  (match f
    ((list '= t1 t2)
     `(= ,(skolemize-term t1 env)
	 ,(skolemize-term t2 env)))
    ((list* rel ts)
     `(,rel . ,(mapcar #'(lambda (v) (skolemize-term v env)) ts)))
    (f (error "Invalid atomic formula ~a" f))))

(defun skolemize- (f bvars env)
  (match f
    ;; base cases
    ((satisfies booleanp) f)
    ((list* op es)
     (cond
      ((pconnectivep op)
       `(,op . ,(mapcar #'(lambda (e) (skolemize- e bvars env)) es)))
      ((equal op 'forall)
       (let ((vars (car es))
	     (body (cadr es)))
	 (let ((e (skolemize- body (append vars bvars)
			      (extend-env/self env vars))))
	   `(forall ,vars ,e))))
      ((equal op 'exists)
       (let ((vars (car es))
	     (body (cadr es)))
	 (let ((new-env
		(if bvars (extend-env/fns env vars bvars)
		  (extend-env/constants env vars))))
	   (skolemize- body bvars new-env))))
      ((atomic-formulap `(,op . ,es))
       (skolemize-atomic-formula f env))
      (t (error "Invalid formula ~a" f))))
    (f (error "Invalid formula ~a" f))))


(defun init-skolem-env (vs)
  (mapcar #'(lambda (x) (cons x (new-constant-symbol))) vs))

(defun skolemize (f)
  (defparameter SKOLEM-COUNTER 11)
  (let ((vs (free-vars f)))
    (skolemize- f nil (init-skolem-env vs))))

;;;;;;;;;;;;;;;;;;;;;;
;; Prenex normal form

;; replace all vars in a term with their new association
(defun replace-in-term (xs term)
  (cond
   ((symbolp term)
    (let ((e (assoc term xs))) (if e (cdr e) term)))
   ((and (consp term) (function-symbolp (car term))
	 `(,(car term) . ,(mapcar #'(lambda (e) (replace-in-term xs e)) (cdr term)))))
   (t term)))

(defun apply-renaming (xs e)
  (match e
    ((list '= f1 f2) `(= ,(replace-in-term xs f1) ,(replace-in-term xs f2)))
    ((list* rel fs) `(,rel . ,(mapcar #'(lambda (e) (replace-in-term xs e)) fs)))
    (t (error "Invalid atomic formula ~a" e))))

(defun find-alts/or (xs used)
  (cond
   ((endp xs) nil)
   ((in (car xs) used)
    (cons (cons (car xs) (new-variable-symbol (car xs)))
	  (find-alts/or (cdr xs) used)))
   (t (cons (cons (car xs) (car xs))
	    (find-alts/or (cdr xs) used)))))


(defun prenex-all/or (fs renaming used acc qs)
  (cond
   ((endp fs) (cons qs `(or . ,acc)))
   (t (let* ((f (car fs))
	     (b-vs (bound-vars f))
	     (new-subst (find-alts/or b-vs used))
	     (f (if new-subst (replace-in new-subst f) f))
	     (new-used (set-binary-union b-vs used)))
	(let* ((v (prenex- f renaming))
	       (new-qs (car v))
	       (f (cdr v)))
	  (prenex-all/or (cdr fs) renaming new-used
			 (snoc f acc)
			 (set-binary-union (mapcar #'cdr new-subst)
					   (set-binary-union qs new-qs))))))))

(defun find-alts/and (xs used options)
  (cond
   ((endp xs) nil)
   ((endp options) nil)
   ((in (car xs) used)
    (cons (cons (car xs) (car xs))
	  (find-alts/and (cdr xs) used options)))
   (t (cons (cons (car xs) (car options))
	    (find-alts/and (cdr xs) used (cdr options))))))

(defun replace-in (xs f)
  (match f
    ((satisfies booleanp) f)
    ((list 'not e) `(not ,(apply-renaming xs e)))
    ((list 'forall vars e)
     `(forall ,(difference vars (mapcar #'car xs))
	      ,(replace-in xs e)))
    ((list* 'and es)
     `(and . ,(mapcar #'(lambda (e) (replace-in xs e)) es)))
    ((list* 'or es)
     `(or . ,(mapcar #'(lambda (e) (replace-in xs e)) es)))
    (f (apply-renaming xs f))))

(defun prenex-all/and (fs renaming used acc qs)
  (cond
   ((endp fs) (cons qs `(and . ,acc)))
   (t (let* ((f (car fs))
	     (b-vs (bound-vars f))
	     (f-vs (free-vars f))
	     (new-subst (find-alts/and b-vs used (difference used (append b-vs f-vs))))
	     (f (if new-subst (replace-in new-subst f) f))
	     (v (prenex- f renaming))
	     (new-qs (car v))
	     (f (cdr v)))
	(prenex-all/and (cdr fs) renaming (set-binary-union b-vs used)
			(snoc f acc) (set-binary-union qs new-qs))))))

;; prenex- returns two things:
;; the prenexed form, and all of the quantifiers needed to complete it.
;; it also assumes that the input formula has been
;; simplified, skolemized, and is in NNF

(defun prenex- (f renaming)
  (match f
    ((satisfies booleanp) (cons nil f))
    ((list 'not e)
     (let ((res (prenex- e renaming)))
       (cons (car res) `(not ,(cdr res)))))
    ((list* 'and es) (prenex-all/and es renaming nil nil nil))
    ((list* 'or es) (prenex-all/or es renaming nil nil nil))
    ((list 'forall vars body)
     (let* ((new-names (extend-fresh vars (mapcar #'car renaming)))
	    (v (prenex- body (append new-names renaming)))
	    (qs (car v))
	    (f (cdr v)))
       (cons (append (mapcar #'cdr new-names) qs) f)))
    ((satisfies atomic-formulap) (cons nil (apply-renaming renaming f)))
    (f (error "Invalid formula ~a" f))))

(defun prenex (f)
  (defparameter PRENEX-COUNTER 11)
  (let ((v (prenex- f nil)))
    (let ((qs (car v))
	  (f (cdr v)))
      (if qs `(forall ,qs ,f) f))))

;;;;;;;;;;;;;;;;;;;
;; Tseitin (conversion of matrix to CNF)

(defun disj-all (es lit)
  (match es
    (nil nil)
    ((cons a d)
     (let ((res (disj-all d lit)))
       (match a
	 (nil (cons lit res))
	 (t (cons t res))
	 ((satisfies atomic-formulap) (cons `(or ,a ,lit) res))
	 ((list 'not e) (cons `(or (not ,e) ,lit) res))
	 ((list* 'and es) (cons `(and . ,(disj-all es lit)) res))
	 ((list* 'or es) (cons `(or . ,(snoc lit es)) res))
	 (a (error "Invalid formula ~a" a)))))))

(defun create-definition (f name vars)
  (let* ((not-f (negate* f)))
    (tseitin-
     `(and ,@(disj-all (list not-f) name)
	   ,@(disj-all (list f) `(not ,name)))
     vars)))

(defun gen-defs (fs acc vars)
  (match fs
   (nil (list acc))
   ((cons a d)
    (match a
      ((satisfies atomic-formulap) (gen-defs d (snoc a acc) vars))
      ((list 'not e) (gen-defs d (snoc `(not ,e) acc) vars))
      (a (let* ((x `(,(new-rel-symbol) . ,vars))
		;; instead of a prop variable, definitions are associated
		;; with no-argument relation symbols
		(def (create-definition a x vars))
		(rst (gen-defs d (snoc x acc) vars)))
	   (snoc def rst)))))))

(defun tseitin- (f vars)
  (match f
    ((satisfies booleanp) f)
    ((satisfies atomic-formulap) f)
    ;; And is easy, but after recurring, simplification
    ;; is necessary in order to flatten everything
    ((list* 'and es)
     (simplify-and (mapcar #'(lambda (e) (tseitin- e vars)) es)))
    ;; Here we need to do work. Create a CNF definition for each subterm of the or.
    ((list* 'or es)
     (simplify-and (gen-defs es '(or) vars)))
    ((list 'not e)
     (match e
       ((satisfies atomic-formulap) `(not ,e))
       ((list 'not e) (tseitin- e vars))
       ((list* 'or es) (tseitin- `(and . ,(mapcar #'negate es)) vars))
       ((list* 'and es) (tseitin- `(or . ,(mapcar #'negate es)) vars))))
    (f (error "Invalid formula ~a" f))))


(defun tseitin (f)
  (defparameter TSEITIN-COUNTER 11)
  (match f
    ((list 'forall vars f)
     `(forall ,vars ,(tseitin- f vars)))
    (f (tseitin- f nil))))

(defun simp-skolem-pnf-cnf (f)
  (tseitin (fo-simplify (prenex (skolemize (nnf (fo-simplify f)))))))

;;; Testing to ensure that the result of simp-skolem-pnf-cnf
;;; has the right properties (cnf & matrix). Because
;;; unufication-resolution can prove that the results are validities
;;; we use that as approximate evidence that the transformation
;;; yields equisatisfiable results.

(defun matrixp (f)
  (match f
    ((satisfies atomic-formulap) t)
    ((list 'not f) (matrixp f))
    ((list* 'and fs)
     (reduce #'(lambda (e ans) (and ans (matrixp e))) fs
	     :from-end t :initial-value t))
    ((list* 'or fs)
     (reduce #'(lambda (e ans) (and ans (matrixp e))) fs
	     :from-end t :initial-value t))
    (_ nil)))

(defun atomic-or-neg (e)
  (match e
    ((satisfies atomic-formulap) t)
    ((list 'not f) (atomic-formulap f))
    (_ nil)))

(defun disjp (f)
  (match f
    ((satisfies atomic-or-neg) t)
    ((list* 'or fs)
     (reduce #'(lambda (e ans) (and ans (atomic-or-neg e))) fs
	     :initial-value t :from-end t))
    (_ nil)))

(defun cnfp (f)
  (match f
    ((satisfies booleanp) t)
    ((satisfies atomic-or-neg) t)
    ((list* 'and fs)
     (reduce #'(lambda (e ans) (and ans (disjp e))) fs
	     :initial-value t :from-end t))
    (_ (disjp f))))


(defun test-simp-skolem-pnf-cnf (f)
  (let ((f (simp-skolem-pnf-cnf f)))
    (let ((m (match f
	       ((list 'forall _ m) m)
	       (_ f))))
      (and (matrixp m) (cnfp m)))))

;; validities from wikipedia, which are used for the evaluator as well

(defparameter test1
    '(iff (not (forall (x) (P x)))
	  (exists (x) (not (P x)))))

(assert (test-simp-skolem-pnf-cnf test1))

(defparameter test2
    '(iff (not (exists (x) (P x)))
	  (forall (x) (not (P x)))))

(assert (test-simp-skolem-pnf-cnf test2))

(defparameter test3
  '(iff (forall (x y) (P x y))
	(forall (y x) (P x y))))

(assert (test-simp-skolem-pnf-cnf test3))

(defparameter test4
  '(iff (exists (x y) (P x y))
	(exists (y x) (P x y))))

(assert (test-simp-skolem-pnf-cnf test4))

(defparameter test5
  '(iff (and (forall (x) (P x))
	     (forall (y) (Q y)))
	(forall (x) (and (P x) (Q x)))))

(assert (test-simp-skolem-pnf-cnf test5))

(defparameter test6
  '(iff (or (exists (x) (P x)) (exists (x) (Q x)))
	(exists (x) (or (P x) (Q x)))))

(assert (test-simp-skolem-pnf-cnf test6))

(defparameter test7
  '(iff (and (implies (natp c1) (R z y))
	     (exists (x) (Q x)))
	(exists (x) (and (implies (natp c1) (R z y))
			 (Q x)))))

(assert (test-simp-skolem-pnf-cnf test7))

(defparameter test8
  '(iff (or (not (forall (x) (P x)))
	    (forall (x) (Q x)))
	(forall (x) (or (not (forall (z) (P z)))
			(Q x)))))

(assert (test-simp-skolem-pnf-cnf test8))

;;; programs from the book

(defparameter barb
  '(not (exists (z) (forall (x) (iff (shaves z x)
				     (not (shaves x x)))))))

(assert (test-simp-skolem-pnf-cnf barb))

(defparameter p38
  '(iff (forall (x)
		(implies (and (P c) 
			      (implies (P x) (exists (y) (and (P y) (R x y)))))
			 (exists (z w) (and (P z) (R x w) (R w z)))))
	(forall (x)
		(and (or (not (P c)) (P x) (exists (z w) (and (P z) (R x w) (R w z))))
		     (or (not (P c)) (not (exists (y) (and (P y) (R x y))))
			 (exists (z w) (and (P z) (R x w) (R w z))))))))

(assert (test-simp-skolem-pnf-cnf p38))

(defparameter p34
  '(iff (iff (exists (x) (forall (y) (iff (P x) (P y))))
	     (iff (exists (x) (Q x)) (forall (y) (Q y))))
	(iff (exists (x) (forall (y) (iff (Q x) (Q y))))
	     (iff (exists (x) (P x)) (forall (y) (P y))))))

;;  this takes 45 seconds
;(time (assert (test-simp-skolem-pnf-cnf p34)))

(defparameter los-formula
  '(implies (and (forall (x y z) (implies (and (P x y) (P y z)) (P x z)))
		 (forall (x y z) (implies (and (Q x y) (Q y z)) (Q x z)))
		 (forall (x y) (implies (Q x y) (Q y x)))
		 (forall (x y) (or (P x y) (Q x y))))
	    (or (forall (x y) (P x y))
		(forall (x y) (Q x y)))))

(assert (test-simp-skolem-pnf-cnf los-formula))

(defparameter ewd1062
  '(implies (and (forall (x) (LTE x x))
		 (forall (x y z) (implies (and (LTE x y) (LTE y z)) (LTE x z)))
		 (forall (x y) (iff (LTE (f x) y) (LTE x (g y)))))
	    (and (forall (x y) (implies (LTE x y) (LTE (f x) (f y))))
		 (forall (x y) (implies (LTE x y) (LTE (g x) (g y)))))))

(assert (test-simp-skolem-pnf-cnf ewd1062))
#|

 Question 4. (15 pts)

 Define unify, a function that given an a non-empty list of pairs,
 where every element of the pair is FO-term, returns an mgu (most
 general unifier) if one exists or the symbol 'fail otherwise.

 An assignment is a list of conses, where car is a variable, the cdr
 is a term and the variables (in the cars) are unique.

 Test your functions using at least 10 interesting inputs. 
 
|#
;; substitution equivalence
(defun find-and-remove (x s acc)
  (cond
   ((endp s) (list nil nil nil))
   ((equal (caar s) x)
    (list t (cdar s) (append acc (cdr s))))
   (t (find-and-remove x (cdr s) (cons (car s) acc)))))

(defun equiv-substp (s1 s2)
  (cond
   ((endp s1) (endp s2))
   (t (let ((x (caar s1))
	    (term (cdar s1)))
	(let ((e (find-and-remove x s2 nil)))
	  (and (car e) (equal (cadr e) term)
	       (equiv-substp (cdr s1) (caddr e))))))))


(defmacro unify-go-on (&rest vs)
  (cond
   ((endp vs) ''fail)
   (t (let ((e (car vs))
	    (d (cdr vs)))
	(let ((f (car e))
	      (args (cdr e)))
	  `(mv-let (b new-l) (,f l nil . ,args)
		   (if (and b (or (not (equal (len l) (len new-l)))
				  (not (endp (difference l new-l)))
				  (not (endp (difference new-l l)))))
		       (unify new-l)
		     (unify-go-on . ,d))))))))

(defmacro deftransition (name test ret &rest args)
  `(defun ,name (l acc . ,args)
     (cond
      ((endp l) (values nil acc))
      (t (let* ((pr (car l))
		(t1 (car pr))
		(t2 (cdr pr)))
	   (if ,test (values t ,ret)
	     (,name (cdr l) (cons pr acc) . ,args)))))))

(defun all-vars (l)
  (reduce #'(lambda (x ans) (and ans (symbolp x) (variable-symbolp x)))
	  l :from-end t :initial-value t))

(defun subst-free-vars (l)
  (reduce #'(lambda (x ans) (set-binary-union ans (free-vars x)))
	  l :from-end t :initial-value nil))

(defun subst-free-vars/more (l)
  (reduce #'(lambda (x ans)
	      (let ((v (car x))
		    (term (cdr x)))
		(set-union ans (free-vars v) (free-vars term))))
	  l :from-end t :initial-value nil))

(defun repl (pr ls)
  (mapcar #'(lambda (x)
	      (cons (replace-in-term `(,pr) (car x))
		    (replace-in-term `(,pr) (cdr x))))
	  ls))

(defun solvedp (l)
  (let ((vars (mapcar #'car l))
	(terms (mapcar #'cdr l)))
    (and (no-dupsp vars)
	 (all-vars vars)
	 (endp (intersection vars (subst-free-vars terms))))))

(deftransition apply-delete (equal t1 t2) (append acc (cdr l)))

(deftransition apply-orient
  (and (variable-symbolp t2)
       (not (variable-symbolp t1)))
  (append (cons (cons t2 t1) (cdr l)) acc))

(deftransition apply-decompose
  (and (consp t1) (consp t2) (equal (car t1) (car t2)))
  (append (mapcar #'cons (cdr t1) (cdr t2)) (cdr l) acc))


(defun apply-eliminate- (l acc f-vs)
  (cond
   ((endp l) (values nil acc))
   (t (let* ((pr (car l))
	     (t1 (car pr))
	     (t2 (cdr pr)))
	(if (and (variable-symbolp t1)
		 (in t1 (difference f-vs (free-vars t2))))
	    (values t (snoc pr (repl pr (append acc (cdr l)))))
	  (apply-eliminate- (cdr l) (cons pr acc) f-vs))))))

(defun apply-eliminate (l acc f-vs l2 b)
  (cond
   ((endp l) (values b l2))
   (t (mv-let
       (b2 v)
       (apply-eliminate- l2 nil f-vs)
       (apply-eliminate (cdr l) nil f-vs v (or b b2))))))

(defun unify (l)
  (cond
   ((solvedp l) l)
   (t (unify-go-on (apply-delete)
	     (apply-orient)
	     (apply-decompose)
	     (apply-eliminate
	      (subst-free-vars/more l) l nil)))))

;;;;;;;;;;;;;;;;;;;;;;
;; Testing unify

;; successful unifications

(assert (equiv-substp
	 (unify '(((append x y) . (append y (append z w)))
		  ((append w z) . (append 2 1))))
	 '((z . 1) (w . 2) (y . (append 1 2)) (x . (append 1 2)))))

(assert (equiv-substp
	 (unify '(((cons x y) . (cons (f z) (g x z)))
		  ((f z) . (f c1))
		  ((g (f w) 1) . (g x 1))))
	 '((z . c1) (y . (g (f c1) c1)) (x . (f c1)) (w . c1))))

(assert (equiv-substp
	 (unify '((x . y) (y . z) (w1 . w1) (z . w) (w . x) (x . 9)))
	 '((x . 9) (y . 9) (z . 9) (w . 9))))

(assert (equiv-substp
	 (unify '(((R x (g y)) . (R (f y) (g z)))
		  ((not (Q c1 w)) . (not (Q y (g z))))))
	 '((y . c1) (z . c1) (x . (f c1)) (w . (g c1)))))

(assert (equiv-substp
	 (unify '(((+ (f z c3) 3) . (+ (f (f w) x) w))
		  ((R z z) . (R z1 (f y)))))
	 '((x . c3) (w . 3) (z . (f 3)) (z1 . (f 3)) (y . 3))))

(assert (equiv-substp
	 (unify '(((not (R x2 x3)) . (not x))
		  (x . (R z y))
		  ((f z (g y)) . (f (not w1) (g c3)))))
	 '((x . (R (not w1) c3))
	   (x3 . c3)
	   (x2 . (not w1))
	   (z . (not w1))
	   (y . c3))))

(assert (equiv-substp
	 (unify '(((R x y z w) . (R y x w z))
		  ((Q c1 y y) . (Q z w z))
		  (x1 . x)))
	 '((x . c1) (x1 . c1) (y . c1) (z . c1) (w . c1))))

;; cases where unification should fail 
(assert (equal 'fail
	       (unify '(((F (g x) c1) . (F (g c1) y))
			((G x) . (G y))
			((f z) . y)))))

(assert (equal 'fail
	       (unify '(((f x y z) . (f y x z))
			((g y z) . (g c2 (f x)))
			(x . c1)))))

(assert (equal 'fail
	       (unify '(((f (A z y)) . (f (A y z)))
			((f z) (f c2))
			((g c1 x) . (g x z))
			(z x)))))

#|

 Question 5. (25 pts)

 Define fo-no=-val, a function that given a FO formula, without equality,
 checks if it is valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement.

 Test your functions using at least 10 interesting inputs
 including the formulas from the following pages of the book: 178
 (p38, p34), 179 (ewd1062), 180 (barb), and 198 (the Los formula).
|#

(defun map-free-vars (ls)
  (reduce #'(lambda (e ans) (set-union (free-vars e) ans)) ls
	  :from-end t :initial-value nil))

(defun map-renaming (ls R)
  (mapcar #'(lambda (e) (apply-renaming R e)) ls))

;; Gettin the matrix out of a universal formula
(defun matrix (f)
  (match f ((list 'forall vars b) b) (f f)))

;; formatting formulas to be sets of sets of literals+negated literals
(defun form-clause (x)
  (match x
    ((satisfies atomic-formulap) `(,x))
    ((list 'not e) `((not ,e)))
    ((list* 'or es) es)))

(defun formula-to-clauses (f)
  (match f
    (t '())
    (nil '(()))
    ((satisfies atomic-formulap) `((,f)))
    ((list* 'or es) `(,es))
    ((list 'not e) `(((not ,e))))
    ((list* 'and es) (mapcar #'form-clause es))))

;; splitting a set of clauses into those that only contain
;; positive literals, and the rest.

(defun all-positivep (K)
  (or (endp K)
      (and (atomic-formulap (car K))
	   (all-positivep (cdr K)))))

(defun split-clauses (K pos oth)
  (cond
   ((endp K) (values pos oth))
   ((all-positivep (car K))
    (split-clauses (cdr K) (cons (car K) pos) oth))
   (t (split-clauses (cdr K) pos (cons (car K) oth)))))

(defun find-matches (neg? rel ls yes)
  (match ls
    (nil yes)
    ((list* (list 'not e) es)
     (if (and neg (equal rel (car e)))
	 (find-matches neg? rel es (cons `(not ,e) yes))
       (find-matches neg? rel es yes)))
    ((list* e es)
     (if (and (not neg?) (equal rel (car e)))
	 (find-matches neg? rel es (cons e yes))
       (find-matches neg? rel es yes)))))

;; returns a list of (list of substitutions and the portion of the k-resolvent
;; coming from D if that subsitution can be successfully unified)

(defun extend-opts (e curr ls)
  (mapcar #'(lambda (a)
	      (let ((s (car a))
		    (k (cadr a)))
		(list (cons `(,e . ,curr) s)
		      (remove curr k :test #'equal))))
	  ls))

(defun link-matches (e es D)
  (cond
   ((endp es) nil)
   (t (let* ((curr (car es))
	     (not-curr (negate curr))
	     (pr (cons e not-curr))
	     (res (link-matches e (cdr es) D)))
	(append (extend-opts e not-curr res)
		res
		(list (list `(,pr) (remove curr D :test #'equal))))))))

(defun extend-k-res (ls Cp)
  (cond
   ((endp ls) nil)
   (t (let* ((v (car ls))
	     (s (car v))
	     (k-res (cadr v)))
	(cons (list s (append Cp k-res))
	      (extend-k-res (cdr ls) Cp))))))

(defun complete (sig k-res ls)
  (reduce #'(lambda (e ans)
	      (let ((sig-e (car e))
		    (k-res-e (cadr e)))
		(cons (list (append sig sig-e) (intersection k-res k-res-e)) ans)))
	  ls :from-end t :initial-value nil))

(defun complete-substs (with without)
  (reduce #'(lambda (e ans) (append (complete (car e) (cadr e) without) ans))
	  with :from-end t :initial-value nil))

(defun complete-withouts (ls t1)
  (mapcar #'(lambda (e)
	      (let ((s (car e))
		    (k (cadr e)))
		(list s (cons t1 k))))
	  ls))


;; to optimally order substitution attempts and negative clauses
(defun res< (e1 e2)
  (let ((k1 (cadr e1))
	(k2 (cadr e2)))
    (< (len k1) (len k2))))

(defun len< (e1 e2)
  (< (len e1) (len e2)))

(defun less (f e ls)
  (cond
   ((endp ls) nil)
   ((apply f (list (car ls) e))
    (cons (car ls) (less f e (cdr ls))))
   (t (less f e (cdr ls)))))

(defun notless (f e ls)
  (cond
   ((endp ls) nil)
   ((not (apply f (list (car ls) e)))
    (cons (car ls) (notless f e (cdr ls))))
   (t (notless f e (cdr ls)))))

(defun qsort (f l)
  (cond
   ((endp l) nil)
   (t (let ((piv (car l)))
	(append (qsort f (less f piv (cdr l)))
		(cons piv (qsort f (notless f piv (cdr l)))))))))

(defun qsort-res< (l) (sort l #'res<))
(defun qsort-len< (l) (sort l #'len<))


(defun make-substs (C D)
  (cond
   ((endp C) nil)
   (t (let ((t1 (car C)))
	(let* ((matches
		(match t1
		       ((list 'not (list* R ts)) (find-matches nil R D nil))
		       ((list* R ts) (find-matches t R D nil))))
	       (C-substs (link-matches t1 matches D))
	       (C-substs (extend-k-res C-substs (cdr C)))
	       (without (make-substs (cdr C) D)))
	  (append (complete-substs C-substs without)
		  (complete-withouts without t1)
		  C-substs))))))

(defun split-batch (n ls)
  (cond
   ((endp ls) (values nil nil))
   (t (let ((a (car ls)))
	(if (> (len (cadr a)) n)
	    (values nil ls)
	  (mv-let
	   (now later)
	   (split-batch n (cdr ls))
	   (values (cons a now) later)))))))

(defun attempt-resolution (options)
  (cond
   ((endp options) nil)
   (t (let ((sigma (caar options))
	    (K-res (cadar options)))
	(let ((sig (unify sigma)))
	  (if (equal sig 'fail)
	      (attempt-resolution (cdr options))
	    (if (endp K-res) (list nil)
	      (cons (map-renaming K-res sig)
		    (attempt-resolution (cdr options))))))))))

(defun try-all (C f-vs Ds)
  (cond
   ((endp ds) nil)
   (t (let* ((D (car Ds))
	     (df-vs (map-free-vars D))
	     (I (intersection f-vs df-vs))
	     (Ren (extend-fresh I I))
	     (D (if (not I) D (map-renaming D Ren)))
	     (sigmas (make-substs C D))
	     (sigmas (qsort-res< sigmas))
	     (listof-k-res (attempt-resolution sigmas)))
	(if (in nil listof-k-res) (list nil)
	  (append listof-k-res (try-all C f-vs (cdr Ds))))))))

(defun gen-all- (C f-vs Ds)
  (cond
   ((endp Ds) nil)
   (t (let* ((D (car Ds))
	     (df-vs (map-free-vars D))
	     (I (intersection f-vs df-vs))
	     (Ren (extend-fresh I I))
	     (D (if (not I) D (map-renaming D Ren)))
	     (sigmas (make-substs C D)))
	(append sigmas (gen-all- C f-vs (cdr Ds)))))))

(defun gen-all (pos neg)
  (cond
   ((endp pos) nil)
   (t (append (gen-all- (car pos) (map-free-vars (car pos)) neg)
	      (gen-all (cdr pos) neg)))))

;; given an atomic formula, replace each variable inside with a number.
;; this way, we can check subsumption as syntactic subset.

(defun extend-num (ren vs i)
  (cond
   ((endp vs) (values ren i))
   (t (let* ((a (car vs)))
	(if (assoc a ren)
	    (extend-num ren (cdr vs) i)
	  (extend-num (cons (cons a i) ren) (cdr vs) (+ 1 i)))))))

(defun gen-deBruijn-renaming (i es repl)
  (cond
   ((endp es) repl)
   (t (let* ((a (car es))
	     (f-vs (free-vars a)))
	(mv-let (repl i)
		(extend-num repl f-vs i)
		(gen-deBruijn-renaming i (cdr es) repl))))))

(defun de-Bruijn~ (at-form)
  (map-renaming at-form (gen-deBruijn-renaming 0 at-form nil)))

(defun check-subsumption (ls C Dg)
  (cond
   ((endp ls) nil)
   (t (let* ((sig (car ls)))
	(let ((v (unify sig)))
	  (if (not (equal v 'fail))
	      (let ((Cg (map-renaming C v)))
		(if (endp (difference Cg Dg)) t
		  (check-subsumption (cdr ls) C Dg)))))))))

(defun get-subsumption-substs (C D)
  (mapcar #'car (make-substs C (mapcar #'negate D))))

(defun subsumes? (C D)
  (let ((D-ground (de-Bruijn~ D)))
    (let ((opts (get-subsumption-substs C D-ground)))
      (check-subsumption opts C D-ground))))

(defun check-subsumed (k ls)
  (reduce #'(lambda (a ans)
	      (if ans ans
		(if (subsumes? a k) (list a)
		  nil)))
	  ls :from-end t :initial-value nil))

(defun check-subsumes (k ls use?)
  (reduce #'(lambda (a ans)
	      (let ((drop? (subsumes? k a)))
		(cond
		 (drop? (if use? (cons k ans) ans))
		 (t (cons a ans)))
		;(cons (if drop? k a) ans)
		))
	  ls :from-end t :initial-value nil))

(defun subsume-replace- (p? k-res pos neg)
  (let ((b (check-subsumed k-res (if p? pos (append pos neg)))))
    (if b (values pos neg)
      (let ((pos (if p? (check-subsumes k-res pos t) pos))
	    (neg (check-subsumes k-res neg (if p? nil t))))
	(if p? (values (cons k-res pos) neg)
	  (values pos (cons k-res neg)))))))

(defun subsume-replace (ks pos neg)
  (cond
   ((endp ks) (values pos neg))
   (t (let* ((k (car ks))
	     (b (all-positivep k)))
	(mv-let (pos neg)
		(subsume-replace- b k pos neg)
		(subsume-replace (cdr ks) pos neg))))))

(defun initial-subsumption-filter- (ls acc)
  (cond
   ((endp ls) acc)
   (t (let ((e (check-subsumed (car ls) acc)))
	(if e
	    (initial-subsumption-filter- (cdr ls) (cons (car e) acc))
	    (initial-subsumption-filter- (cdr ls) (cons (car ls) acc)))))))

(defun initial-subsumption-filter (ls)
  (initial-subsumption-filter- ls nil))

(defun manage-options (n ops)
  (cond
   ((endp ops) nil)
   (t (mv-let
       (now later)
       (split-batch n ops)
       (let ((v (attempt-resolution now)))
	 (if (in nil v) (list nil)
	   (append v (manage-options (+ n 1) later))))))))

(defun U-res (pos neg)
  (cond
   ((endp pos) 'sat)
   ((endp neg) 'sat)
   (t (let ((options (qsort-res< (gen-all pos neg))))
	(let ((listof-k-res (manage-options 0 options)))
	 (if (in nil listof-k-res) 'unsat
	   (mv-let
	    (pos neg)
	    (subsume-replace listof-k-res pos neg)
	    (U-res pos neg))))))))


(defun fo-no=-val (f)
  (print "Performing simplification, skolemization, prenex, and tseitin")
  (let ((psi (simp-skolem-pnf-cnf `(not ,f))))
    (if (booleanp psi) (if psi 'not-valid 'valid)
      (let* ((m (matrix psi))
	     (K (formula-to-clauses m)))
	(print "Minimizing initial clauses using subsumption analysis")
	(let ((K (remove-dups (initial-subsumption-filter (qsort-len< K)))))
	  (mv-let (pos neg) (split-clauses K nil nil)
		  (progn
		    (print "The initial sets of clauses are:")
		    (print pos)
		    (print neg)
		    (print "starting U-resolution")
		    (let ((res (U-res pos neg)))
		      (match res
			     ('sat 'not-valid)
			     ('unsat 'valid))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Modified implementation, based on Book code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-substs- (C D)
  (cond
   ((endp C) nil)
   (t (let ((t1 (car C)))
	(let* ((matches
		(match t1
		       ((list 'not (list* R ts)) (find-matches nil R D nil))
		       ((list* R ts) (find-matches t R D nil))))
	       (C-substs (link-matches t1 matches D))
	       (C-substs (extend-k-res C-substs (cdr C)))
	       (without (make-substs- (cdr C) D)))
	  (append (complete-substs C-substs without)
		  (complete-withouts without t1)
		  C-substs))))))

;; guard for positive resolution
(defun make-substs (C D)
  (if (and (not (all-positivep C))
	   (not (all-positivep D)))
      nil (make-substs- C D)))

(defun resolve-all (cls ls)
  (cond
   ((endp ls) nil)
   (t (append (attempt-resolution (make-substs cls (car ls)))
	      (resolve-all cls (cdr ls))))))

(defun subsumption-check (ls acc)
  (cond
   ((endp ls) acc)
   (t (let ((e (check-subsumed (car ls) acc)))
	(if e
	    (initial-subsumption-filter- (cdr ls) (cons (car e) acc))
	    (initial-subsumption-filter- (cdr ls) (cons (car ls) acc)))))))

(defun initial-subsumption-filter (ls)
  (initial-subsumption-filter- ls nil))

(defun add-if-not-subsumed (old new acc)
  (cond
   ((endp new) (append old acc))
   ((check-subsumed (car new) old) (add-if-not-subsumed old (cdr new) acc))
   (t (add-if-not-subsumed old (cdr new) (cons (car new) acc)))))

(defun U-res (used unused)
  (cond
   ((endp unused) (error "Couldn't find a proof"))
   (t (let* ((cls (car unused))
	     (used (cons cls used))
	     (news (resolve-all cls used)))
	(if (in nil news) 'valid
	  (U-res used (add-if-not-subsumed (cdr unused) news nil)))))))

(defun fo-no=-val (f)
  (print "Performing simplification, skolemization, prenex, and tseitin")
  (let ((psi (simp-skolem-pnf-cnf `(not ,f))))
    (if (booleanp psi) (if psi 'not-valid 'valid)
      (let* ((m (matrix psi))
	     (K (formula-to-clauses m)))
	(print "Minimizing initial clauses using subsumption analysis")
	(let ((K (remove-dups (initial-subsumption-filter (qsort-len< K)))))
	  (progn
	    (print "The initial clauses are:")
	    (print K)
	    (print "starting U-resolution")
	    (U-res nil K)))))))



;; The exam problem -- my old implementation found a solution,
;; but my solution doesn't
(defparameter examQ4
  '(not (forall (x y z)
		(and (or (R x (f y z)) (P (f y z) (f y x)))
		     (or (not (P x y)) (Q y x))
		     (or (R y x) (not (Q x y)))
		     (or (P x z) (not (R x z)))
		     (or (not (Q (f x y) z)))))))

; 25 seconds
(time (assert (equal 'valid (fo-no=-val examQ4))))


;; testing on simple validities from Wikipedia
;; (same as tests for simp-skolem-pnf-cnf)

(defparameter test1
    '(iff (not (forall (x) (P x)))
	  (exists (x) (not (P x)))))

(defparameter test2
    '(iff (not (exists (x) (P x)))
	  (forall (x) (not (P x)))))

(defparameter test3
  '(iff (forall (x y) (P x y))
	(forall (y x) (P x y))))

(defparameter test4
  '(iff (exists (x y) (P x y))
	(exists (y x) (P x y))))

(defparameter test5
  '(iff (and (forall (x) (P x))
	     (forall (y) (Q y)))
	(forall (x) (and (P x) (Q x)))))

(defparameter test6
  '(iff (or (exists (x) (P x)) (exists (x) (Q x)))
	(exists (x) (or (P x) (Q x)))))

; These pass quickly
(assert (equal 'valid (fo-no=-val test1)))
(assert (equal 'valid (fo-no=-val test2)))

; 3 seconds
(time (assert (equal 'valid (fo-no=-val test3))))
(time (assert (equal 'valid (fo-no=-val test4))))

;; These are slower

; 21 secs 
(time (assert (equal 'valid (fo-no=-val test5))))

; 35 secs
(time (assert (equal 'valid (fo-no=-val test6))))

(defparameter test7
  '(iff (and (implies (natp c1) (R z y))
	     (exists (x) (Q x)))
	(exists (x) (and (implies (natp c1) (R z y))
			 (Q x)))))

(defparameter test8
  '(iff (and (implies (not (or (natp c1) (symbolp c1))) (R z y))
	     (exists (x) (Q x)))
	(exists (x) (and (implies (not (or (natp c1) (symbolp c1))) (R z y))
			 (Q x)))))

(defparameter test9
  '(iff (or (R c1 c2)
	    (forall (x) (Q x)))
	(forall (x)
		(or (R c1 c2)
		    (Q x)))))

(defparameter test10
  '(iff (or (not (forall (z) (not (R z c2))))
	    (forall (x) (Q x)))
	(forall (x)
		(or (not (forall (z) (not (R z c2))))
		    (Q x)))))

;  secs
(time (assert (equal 'valid (fo-no=-val test7))))
;  secs
(time (assert (equal 'valid (fo-no=-val test8))))


; 24 secs
(time (assert (equal 'valid (fo-no=-val test9))))

; 30 secs
(time (assert (equal 'valid (fo-no=-val test10))))


;; Other book problems
(defparameter prawitz
  '(implies (forall (x y) (exists (z) (forall (w) (implies (and (P x) (Q y))
							   (and (R z) (QQ w))))))
	    (exists (x y) (implies (and (P x) (Q y)) (exists (z) (R z))))))

; 2.4 secs
(time (assert (equal 'valid (fo-no=-val prawitz))))

;;;;;;;;;;;;;;
;; Required Test programs from the book

; 180 (barb)

;; passes quickly
(defparameter barb
  '(not (exists (z) (forall (x) (iff (shaves z x)
				     (not (shaves x x)))))))
;; really quick
(time (assert (equal 'valid (fo-no=-val barb))))

;178 (p38, p34), 

(defparameter p38
  '(iff (forall (x)
		(implies (and (P c) 
			      (implies (P x) (exists (y) (and (P y) (R x y)))))
			 (exists (z w) (and (P z) (R x w) (R w z)))))
	(forall (x)
		(and (or (not (P c)) (P x) (exists (z w) (and (P z) (R x w) (R w z))))
		     (or (not (P c)) (not (exists (y) (and (P y) (R x y))))
			 (exists (z w) (and (P z) (R x w) (R w z))))))))

(time (assert (equal 'valid (fo-no=-val p38))))

(defparameter p34
  '(iff (iff (exists (x) (forall (y) (iff (P x) (P y))))
	     (iff (exists (x) (Q x)) (forall (y) (Q y))))
	(iff (exists (x) (forall (y) (iff (Q x) (Q y))))
	     (iff (exists (x) (P x)) (forall (y) (P y))))))

;(time (assert (equal 'valid (fo-no=-val p34))))

;;179 (ewd1062)

(defparameter ewd1062
  '(implies (and (forall (x) (LTE x x))
		 (forall (x y z) (implies (and (LTE x y) (LTE y z)) (LTE x z)))
		 (forall (x y) (iff (LTE (f x) y) (LTE x (g y)))))
	    (and (forall (x y) (implies (LTE x y) (LTE (f x) (f y))))
		 (forall (x y) (implies (LTE x y) (LTE (g x) (g y)))))))

(time (assert (equal 'valid (fo-no=-val ewd1062))))

;198 (the Los formula)
(defparameter los-formula
  '(implies (and (forall (x y z) (implies (and (P x y) (P y z)) (P x z)))
		 (forall (x y z) (implies (and (Q x y) (Q y z)) (Q x z)))
		 (forall (x y) (implies (Q x y) (Q y x)))
		 (forall (x y) (or (P x y) (Q x y))))
	    (or (forall (x y) (P x y))
		(forall (x y) (Q x y)))))

(assert (equal 'valid (fo-no=-val los-formula))) 

#|

 Question 6. Extra Credit (15 pts)

 Define fo-val, a function that given a FO formula, checks if it is
 valid using U-Resolution.

 If it is valid, return 'valid.

 Your code should use positive resolution and must implement
 subsumption and replacement. This is an extension of question 5,
 where you replace equality with a new relation symbol and add
 the appropriate equivalence and congruence hypotheses.
|#

(defparameter equality-rel 'EQUALITY)
(defparameter default-eq-clauses
  `(((,equality-rel x x))
    ((not (,equality-rel x y))
     (,equality-rel y x))
    ((not (,equality-rel x y))
     (not (,equality-rel y z))
     (,equality-rel x z))))

(defun replace-equality (f)
  (match f
    ((satisfies booleanp) f)
    ((list '= e1 e2) `(,equality-rel ,e1 ,e2))
    ((satisfies atomic-formulap) f)
    ((list 'forall vars f) `(forall ,vars ,(replace-equality f)))
    ((list 'exists vars f) `(exists ,vars ,(replace-equality f)))
    ((list* op es)
     (if (pconnectivep op)
	 `(,op . ,(mapcar #'replace-equality es))
       (error "Invalid formula ~a" f)))))

(defun var-list (n v)
  (cond
   ((equal n 0) nil)
   (t (cons (new-variable-symbol v)
	    (var-list (- n 1) v)))))

(defun fn-equality (ls)
  (mapcar
   #'(lambda (x)
       (let ((sym (car x))
	     (xs (var-list (cdr x) 'X))
	     (ys (var-list (cdr x) 'Y)))
	 (snoc `(,equality-rel (,sym . ,xs) (,sym . ,ys))
	       (mapcar #'(lambda (a b)
			   `(not (,equality-rel ,a ,b)))
		       xs ys))))
   ls))

(defun rel-equality (ls)
  (mapcar
   #'(lambda (x)
       (let ((sym (car x))
	     (xs (var-list (cdr x) 'X))
	     (ys (var-list (cdr x) 'Y)))
	 (append (mapcar #'(lambda (a b)
			     `(not (,equality-rel ,a ,b)))
			 xs ys)
		 `((not (,sym . ,xs))
		   (,sym . ,ys)))))
   ls))

(defun gen-equality-clauses (fs rs)
  (defparameter PRENEX-COUNTER 11)
  (append default-eq-clauses
   (fn-equality fs)
   (rel-equality rs)))

(defun fo-val (f)
  (mv-let
   (v fsig rsig)
   (fo-formulap f nil nil)
   (if (not v) (error "Invalid FO formula ~a" f)
     (let ((f-no-eq (replace-equality `(not ,f)))
	   (EQ (gen-equality-clauses fsig rsig)))
       (let ((psi (simp-skolem-pnf-cnf f-no-eq)))
	 (let* ((m (matrix psi))
		(K (formula-to-clauses m))
		(K (remove-dups (append EQ K))))
	   (mv-let
	    (pos neg) (split-clauses K nil nil)
	    (progn
	      (print pos) (print neg)
	      (print "beginning U-resolution")
	      (let ((res (U-res pos neg)))
		(match res
		  ('sat 'not-valid)
		  ('unsat 'valid)))))))))))

(time (assert (equal 'valid (fo-val '(forall (x) (exists (y) (= x y)))))))

(time (assert (equal 'valid (fo-val '(forall (x y) (iff (= x y) (= y x))))))) 

(time (assert (equal 'valid (fo-val
			     '(implies (exists (x y) (not (= x y)))
				       (exists (x) (not (= x c1))))))))

;; 22 seconds
(time (assert (equal 'valid (fo-val
			     '(forall (x y) (exists (z1 z2)
						    (implies (= z1 z2)
							     (iff (R x y z1)
								  (R x y z2)))))))))
;; 26 seconds
(time (assert (equal 'valid (fo-val
			     '(forall (x y) (forall (z1 z2)
						    (implies (= z1 z2)
							     (iff (R x y z1)
								  (R x y z2)))))))))

;; 80 seconds
(time (assert (equal 'valid (fo-val
			     '(forall (x y z)
				      (implies (not (exists (w x) (not (= w x))))
					       (iff (= z y) t (= y z) (= x z))))))))

#|

 Question 7. Extra Credit (25 pts)

 Define horn-sat. It is a function that takes as input

 (1) hs, a list of positive universal Horn sentences and 
 (2) e, a sentence of the form (exists vars (and ...))
     where ... is a list of atomic formulas

 You can assume none of the inputs formulas contain =, if you wish.
 If you solved q5, you can also deal with =. 

 If hs |= e, then horn-sat returns an assignment, sigma, s.t.

 hs |= (and ...)sigma

 Recall that an assignment is defined in Q4.

 |#

(defun do-loop (rules g env)
  (cond
   ((endp rules) env)
   (t (let* ((rule (car rules))
	     (rule (deBruijn~ rule))
	     (c (car rule))
	     (asm (cdr rule))
	     (res (unify `((,c . ,g) . ,env))))
	(if (equal res 'fail)
	    (do-loop (cdr rules) g env)
	  (horn-loop rules res gs))))))

(defun horn-loop (rules env goals)
  (match goals
    (nil env)
    ((cons g1 gs)
     (horn-loop rules (do-loop rules g1 env) gs))))

(defun parse-rule (f)
  (match f
    ((list 'forall vars phi) (parse-rule f))
    ((satisfies atomic-formulap) (list f))
    ((list 'implies (list* 'and es) phi)
     (cons phi es))))


(defun horn-sat (hs e)
  (let ((rules (mapcar #'parse-rule hs)))
    (horn-loop rules env goals)))
