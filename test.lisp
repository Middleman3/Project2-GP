(defvar num-tree '(1 (2 3) (4 5 (6 (7 8 9 10)) 11)))
(defvar nega-tree '(-1 (-2 -3) (-4 -5 (-6 (-7 -8 -9 -10)) -11)))
(defvar num 5)
(defparameter *debug* 2)
(setf num-tree '(1 (2 3) (4 5 (6 (7 8 9 10)) 11)))

(defun test ()
	   (gp-symbolic-regression-setup)
	   (let ((result (subtree-mutation tree)))
	     (print result)
	     (print (num-nodes result))))

(defun run-tests (&key (count 10) (start 7))
	   (setf results '())
	   (gp-symbolic-regression-setup)
	   (setf tree (ptc2 start))
	   (dotimes (x count results)
	     (setf results (append results (list (test))))))

