

(defun matrixp (f)
  (match f
    ((satisfies atomic-formulap) t)
    ((list 'not f) (matrixp f))
    ((list* 'and fs)
     (reduce #'(lambda (e ans) (and ans (matrixp e))) fs
	     :from-ent t :initial-value t))
    ((list* 'or fs)
     (reduce #'(lambda (e ans) (and ans (matrixp e))) fs
	     :from-ent t :initial-value t))
    (_ nil)))
