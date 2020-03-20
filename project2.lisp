;;; This is the "extended" version of Project 1

#|
In this project you will produce three things:

1. A high-level evolutionary computation framework

2. The representation, breeding functions, and evaluations to do a simple
GA for boolean vectors and for floating-point vectors, including a few test
functions on each.

3. The representation, breeding functions, and evaluations to do GP for
two problems:
A. Symbolic Regression
B. Artificial Ant

The high-level EC system will work as follows:

- Simple generational evolution
- GA-style Tournament selection
- A simple breeding function
- some simple statistics functions

I have provided the approximate function templates I myself used to complete
the task; with permission you can use these or go your own way, but otherwise
please try not to deviate much from this template.

The project is due approximately two and a half weeks from now or so.  Please
try to get it in on time.

WHAT YOU MUST PROVIDE:

1. Completed code which works and compiles.  As simple as possible would be nice.

2. A short report describing the code you wrote and some experimentation with it.
Some things to try:
   -- different problems (in the vector section)
   -- different settings of mutation and crossover parameters
   -- different population sizes or run lengths
Try to get a handle on how problem difficulty changes when you tweak various
parameters.  Can you get mutation and crossover parameters which seem optimal for
a given problem for example?  (Obviously bigger population sizes are more optimal
but that's kinda cheating).  Note that this is a STOCHASTIC problem so you'll need
to run a number of times and get the mean best result in order to say anything of
consequence.  It'd be nice if the report were in LaTeX and it'd be good practice for
you as well, but it's not necessary.  I do not accept reports in Word.  Only send
me a PDF.

Make sure your code is compiled.  In most cases (such as SBCL), your code will be
automatically compiled.  But there exist systems (like LispWorks ("lisp" on
mason.gmu.edu)) where the default is to interpret the code, and so you must
compile your file first and then load that.

Information on compiling code and doing compiler optimizations can be found in the
"Speed" chapter of Graham.
|#

(defparameter *boolean-crossover-probability* 0.2)
(defparameter *boolean-mutation-probability* 0.01)
(defparameter *boolean-vector-length* 100)
(defparameter *boolean-mutation-variance* 0.01)

(defparameter *boolean-problem* :max-ones)

(defparameter *float-vector-length* 100)
(defparameter *float-problem :rastrigin)
(defparameter *float-min* -5.12)  ;; these will change based on the problem
(defparameter *float-max* 5.12)   ;; likewise

(defparameter *float-crossover-probability* 0.2)
(defparameter *float-mutation-probability* 0.1)   ;; I just made up this number
(defparameter *float-mutation-variance* 0.01)     ;; I just made up this number

(defparameter *size-limit* 20)
(defparameter *restrict-size* '())
(defparameter *mutation-size-limit* 10)

(defparameter *num-vals* 20)
(defparameter *vals* nil) ;; gets set in gp-setup

(defparameter *x* nil) ;; to be set in gp-evaluator


(defparameter *is-numeric* nil)

(defparameter *map-str-copy* '())
(defparameter *map-strs* '(
".###............................"
"...#............................"
"...#.....................###...."
"...#....................#....#.."
"...#....................#....#.."
"...####.#####........##........."
"............#................#.."
"............#.......#..........."
"............#.......#..........."
"............#.......#........#.."
"....................#..........."
"............#..................."
"............#................#.."
"............#.......#..........."
"............#.......#.....###..."
".................#.....#........"
"................................"
"............#..................."
"............#...#.......#......."
"............#...#..........#...."
"............#...#..............."
"............#...#..............."
"............#.............#....."
"............#..........#........"
"...##..#####....#..............."
".#..............#..............."
".#..............#..............."
".#......#######................."
".#.....#........................"
".......#........................"
"..####.........................."
"................................"))

(defconstant *n* 0)                                                                                 
(defconstant *e* 1)                                                                                 
(defconstant *s* 2)                                                                                 
(defconstant *w* 3) 

(defparameter *map-height* 32)
(defparameter *map-width* 32)

(defparameter *current-move* 0 "The move # that the ant is at right now")
(defparameter *num-moves* 600 "How many moves the ant may make")
(defparameter *current-x-pos* 0 "The current X position of the ant")
(defparameter *current-y-pos* 0 "The current Y position of the ant")
(defparameter *current-ant-dir* *e* "The current direction the ant is facing")
(defparameter *eaten-pellets* 0 "How many pellets the ant has eaten so far")
(defparameter *map-strs-copy* (copy-seq *map-strs*))

(defparameter *nonterminal-set* nil)
(defparameter *terminal-set* nil)

(defun max-ones (vector)
  (let ((count 0))
    (dolist (element vector)
      (if element
	  (setf count (+ count 1))))
    (return-from max-ones count)))

(defun trap (vector)
  (let ((count 0))
    (dolist (element vector)
      (if (not element)
	  (setf count (+ count 1))))

    (if (= count 0)
	(return-from trap (+ (length vector) 1))
	(return-from trap count))))

(defun leading-ones (vector)
  (let ((count 0) (run T))
    (dolist (element vector)
      (if run
	  (if element
	      (setf count (+ count 1))
	      (setf run nil))))
    (return-from leading-ones count)))

(defun leading-ones-blocks (vector b)
  (let ((count 0) (ones-count 0))
    (dolist (element vector)
      (if element
	  (progn
	    (setf ones-count (+ ones-count 1))
	    (if (= ones-count b)
		(progn
		  (setf count (+ count 1))
		  (setf ones-count 0))))))
    (return-from leading-ones-blocks count)))

(defparameter *boolean-fitness* #'max-ones)
(defparameter *float-fitness* #'max-ones)

;;; Useful Functions and Macros

(defmacro swap (elt1 elt2)
  "Swaps elt1 and elt2, using SETF.  Returns nil."
  (let ((temp (gensym)))
    `(let ((,temp ,elt1))
       (setf ,elt1 ,elt2)
       (setf ,elt2 ,temp)
       nil)))

(defmacro while (test return-value &body body)
  "Repeatedly executes body as long as test returns true.
Then evaluates and returns return-value"
  `(progn (loop while ,test do (progn ,@body)) ,return-value))

(defun random-elt (sequence)
  "Returns a random element from sequence"
  (elt sequence (random (length sequence))))

(defun random? (&optional (prob 0.5))
  "Tosses a coin of prob probability of coming up heads,
then returns t if it's heads, else nil."
  (< (random 1.0) prob))

(defun generate-list (num function &optional no-duplicates)
  "Generates a list of size NUM, with each element created by
  (funcall FUNCTION).  If no-duplicates is t, then no duplicates
are permitted (FUNCTION is repeatedly called until a unique
new slot is created).  EQUALP is the test used for duplicates."
  (let (bag)
    (while (< (length bag) num) bag
      (let ((candidate (funcall function)))
	(unless (and no-duplicates
		     (member candidate bag :test #'equalp))
	  (push candidate bag))))))

;;;;;; TOP-LEVEL EVOLUTIONARY COMPUTATION FUNCTIONS

;;; TOURNAMENT SELECTION

(defparameter *tournament-size* 7)
(defun tournament-select-one (population fitnesses)
  ;;; See Algorithm 32 of Essentials of Metaheuristics
  "Does one tournament selection and returns the selected individual."
    (let* ((n (list-length population)) (bestIndex (random (- n 1))))
    (if (/= n (list-length fitnesses)) (error "population size ~D /= fitnesses size ~D" n (list-length fitnesses)))

    (dotimes (i (- *tournament-size* 1) (elt population bestIndex))
      (let ((nextIndex (random (- n 1))))
	(if (> (elt fitnesses nextIndex) (elt fitnesses bestIndex)) (setf bestIndex nextIndex))))))

(defun tournament-selector (num population fitnesses)
  "Does NUM tournament selections, and puts them all in a list"
  (generate-list num (lambda () (tournament-select-one population fitnesses))))

(defun simple-printer (pop fitnesses)  ;; I'm nice and am providing this for you.  :-)
  "Determines the individual in pop with the best (highest) fitness, then
prints that fitness and individual in a pleasing manner."
  (let (best-ind best-fit)
    (mapcar #'(lambda (ind fit)
		(when (or (not best-ind)
			  (< best-fit fit))
		  (setq best-ind ind)
		  (setq best-fit fit))) pop fitnesses)
    (format t "~%Best Individual of Generation...~%Fitness: ~a~%Individual:~a~%"
	    best-fit best-ind)
    fitnesses))

(defparameter *tournament-size* 2)
(defparameter *debug* nil)
(defparameter *alpha* 0.1)
(defparameter *dynamic* nil)
(defparameter *record* nil)

;;;;;; BOOLEAN VECTOR GENETIC ALGORTITHM

;;; Creator, Modifier, Evaluator, and Setup functions for the
;;; boolean vectors Problem.  Assume that you are evolving a bit vector
;;; *vector-length* long.

;;; The default test function is Max-Ones.
;;;; Max-ones is defined in section 11.2.1 of "Essentials of Metaheuristics"
;;; by yours truly.  In that section are defined several other boolean functions
;;; which you should also try and report on.  Some plausible ones might
;;; include:

;;; :max-ones
;;; :trap
;;; :leading-ones
;;; :leading-ones-blocks

(defun uniform-crossover (ind1 ind2 &key (length *boolean-vector-length*) (crossover-probability *boolean-crossover-probability*))
  "Performs uniform crossover on the two individuals, modifying them in place.
*crossover-probability* is the probability that any given allele will crossover.
The individuals are guaranteed to be the same length.  Returns NIL."
  (dotimes (i (- length 1))
    (if (random? crossover-probability)
	(rotatef (elt ind1 i) (elt ind2 i)))))

(defun boolean-vector-creator ()
  "Creates a boolean-vector *boolean-vector-length* in size, filled with
random Ts and NILs, or with random 1s and 0s, your option."
  (generate-list *boolean-vector-length* (lambda () (if (random?) T '()))))

(defun mutate-boolean-vector (ind &key (mutateProb *boolean-mutation-probability*))
  "flips the bit of any allele with mutateProb"
  (dolist (allele ind ind)
    (if (random? mutateProb) (setf allele (not allele)))))

(defun boolean-vector-modifier (ind1 ind2)
  "Copies and modifies ind1 and ind2 by crossing them over with a uniform crossover,
then mutates the children.  *crossover-probability* is the probability that any
given allele will crossover.  *mutation-probability* is the probability that any
given allele in a child will mutate.  Mutation simply flips the bit of the allele."
  (let* ((new1 (copy-list ind1))
	 (new2 (copy-list ind2)))
    (uniform-crossover new1 new2)
    (list (mutate-boolean-vector new1) (mutate-boolean-vector new2))))

(defun boolean-vector-evaluator (ind1)
  "Evaluates an individual, which must be a boolean-vector, and returns
its fitness."
  (funcall *boolean-fitness* ind1))

(defun boolean-vector-sum-setup (&key debug crossProb mutateProb mutateVar tourny min max length alpha dynamic record)
  "Does nothing.  Perhaps you might use this function to set
(ahem) various global variables which define the problem being evaluated
and the floating-point ranges involved, etc.  I dunno."
  (if debug (setf *debug* debug))
  (if crossProb (setf *boolean-crossover-probability* crossProb))
  (if mutateProb (setf *boolean-mutation-probability* mutateProb))
  (if mutateVar (setf *boolean-mutation-variance* mutateVar))
  (if tourny (setf *tournament-size* tourny))
  (if min (setf *float-min* min))
  (if max (setf *float-max* max))
  (if length (setf *boolean-vector-length* length))
  (if alpha (setf *alpha* alpha))
  (if dynamic (setf *dynamic* dynamic))
  (if record (setf *record* record)))

#|
(evolve 50 100
 	:setup #'boolean-vector-sum-setup
	:creator #'boolean-vector-creator
	:selector #'tournament-selector
	:modifier #'boolean-vector-modifier
        :evaluator #'boolean-vector-evaluator
	:printer #'simple-printer
        :mutate-prob *boolean-mutation-probability*)
|#

;;;;;; FLOATING-POINT VECTOR GENETIC ALGORTITHM

;;; Creator, Modifier, Evaluator, and Setup functions for the
;;; GA Max-ONES Problem.  Assume that you are evolving a vector
;;; of floating-point numbers *float-vector-length* long.

;;; The default test function is Rastrigin.
;;;; Rastrigin is defined in section 11.2.2 of "Essentials of Metaheuristics"
;;; by yours truly.  In that section are defined several other floating-point functions
;;; which you should also try and report on.  Some plausible ones might
;;; include:

;;; :rastrigin
;;; :rosenbrock
;;; :griewank
;;; :schwefel

;;; If you were really into this, you might also try testing on
;;; rotated problems -- some of the problems above are linearly
;;; separable and rotation makes them harder and more interesting.
;;; See the end of Section 11.2.2.

;;; I have defined the minimum and maximum gene values for rastrigin
;;; as [-5.12, 5.12].  Other problems have other traditional min/max
;;; values, consult Section 11.2.2.

(defun betweenp (small med large)
  (and (< small med) (< med large))) 

(defun gaussian-random (mean variance)
  "Generates a random number under a gaussian distribution with the given mean and variance (using the Box-Muller-Marsaglia method)"
  (let (x y (w 0))
    (while (not (and (< 0 w) (< w 1))) '()
           (setf x (- (random 2.0) 1.0))
           (setf y (- (random 2.0) 1.0))
           (setf w (+ (* x x) (* y y))))
    (+ mean (* x (sqrt variance) (sqrt (* -2 (/ (log w) w)))))))

(defun gaussian-convolution (ind)
  "Performs gaussian convolution mutation on the individual, modifying it in place.
 Returns NIL."
  (dotimes (i (- (list-length ind) 1) ind)
    (let* ((mean (+ *float-min* (/ (abs (- *float-max* *float-min*)) 2)))
	   (n *float-min*)
	   (out-of-bounds t))
      ;(format t "Individual ~D: ~A" i e)
      (if (random? *float-mutation-probability*)
	  (progn
	    (while out-of-bounds
	      ;(format t "~%~%E=~F  N=~F~%~F < ~F < ~F~%~%" (elt ind i) n *float-min* (+ (elt ind i) n) *float-max*))
	      (setf n (gaussian-random mean *float-mutation-variance*))
	      (if (and (> (+ (elt ind i) n) *float-min*) (< (+ (elt ind i) n) *float-max*))
		  (setf out-of-bounds nil)))
	    (setf (elt ind i) (+ (elt ind i) n)))))))

(defun float-vector-creator ()
  "Creates a floating-point-vector *float-vector-length* in size, filled with
random numbers in the range appropriate to the given problem"
  (let ((domain-length (- *float-max* *float-min*)))
    (generate-list *float-vector-length* (lambda () (+ (random domain-length) *float-min*)))))

(defun float-vector-modifier (ind1 ind2)
  "Copies and modifies ind1 and ind2 by crossing them over with a uniform crossover,
then mutates the children.  *crossover-probability* is the probability that any
given allele will crossover.  *mutation-probability* is the probability that any
given allele in a child will mutate.  Mutation does gaussian convolution on the allele."

  (let* ((new1 (copy-list ind1))
	 (new2 (copy-list ind2)))
    (uniform-crossover new1 new2)
    (gaussian-convolution new1)
    (gaussian-convolution new2)
    (list new1 new2)))

(defun float-vector-sum-evaluator (ind1 &key (fitness-function *float-fitness*))
  "Evaluates an individual, which must be a floating point vector, and returns
its fitness."
  (funcall fitness-function ind1))

(defun float-vector-sum-setup (&key debug crossProb mutateProb mutateVar tourny min max length alpha dynamic record)
  (if debug (setf *debug* debug))
  (if crossProb (setf *float-crossover-probability* crossProb))
  (if mutateProb (setf *float-mutation-probability* mutateProb))
  (if mutateVar (setf *float-mutation-variance* mutateVar))
  (if tourny (setf *tournament-size* tourny))
  (if min (setf *float-min* min))
  (if max (setf *float-max* max))
  (if length (setf *float-vector-length* length))
  (if alpha (setf *alpha* alpha))
  (if dynamic (setf *dynamic* dynamic))
  (if record (setf *record* record)))

(defun evolve (generations pop-size &key setup creator selector modifier evaluator printer mutate-prob)
  "Evolves for some number of GENERATIONS, creating a population of size
POP-SIZE, using various functions"

  ;; The functions passed in are as follows:
  ;;(SETUP)                     called at the beginning of evolution, to set up
  ;;                            global variables as necessary
  ;;(CREATOR)                   creates a random individual
  ;;(SELECTOR num pop fitneses) given a population and a list of corresponding fitnesses,
  ;;                            selects and returns NUM individuals as a list.
  ;;                            An individual may appear more than once in the list.
  ;;(MODIFIER ind1 ind2)        modifies individuals ind1 and ind2 by crossing them
  ;;                            over and mutating them.  Returns the two children
  ;;                            as a list: (child1 child2).  Nondestructive to
  ;;                            ind1 and ind2.
  ;;(PRINTER pop fitnesses)     prints the best individual in the population, plus
  ;;                            its fitness, and any other interesting statistics
  ;;                            you think interesting for that generation.
  ;;(EVALUATOR individual)      evaluates an individual, and returns its fitness.
  ;;Pop will be guaranteed to be a multiple of 2 in size.
  ;;
  ;; HIGHER FITNESSES ARE BETTER

  ;; your function should call PRINTER each generation, and also print out or the
  ;; best individual discovered over the whole run at the end, plus its fitness
  ;; and any other statistics you think might be nifty.

  ;;; HINTS: You could do this in many ways.  But I implemented it using
  ;;; the following functions (among others)
  ;;;
  ;;; FUNCALL FORMAT MAPCAR LAMBDA APPLY

  (funcall setup :record nil)
  (let* ((population (generate-list pop-size creator t))
	 (fitnesses (mapcar evaluator population))
	  chosen offspring bestIndex (maxFitness 0) (deltaFitness 0) (i 0)) ;<for selection 1>

    (dotimes (gen generations)

      ; Calculate change in best fitness
      (setf deltaFitness (abs (- maxFitness (setf maxFitness (apply #'max 0 fitnesses)))))      
      
      ;;; modify mutation rate
      (if *dynamic* (setf mutate-prob (if (> 1 mutate-prob)
				       (+ mutate-prob (* *alpha* (if (< deltaFitness 1) (- 1 deltaFitness) 0)))
				       1)))
      
      ; get some statistics // c-5 = list of quantity of values >5 per individual                 
      (if *is-numeric*
	  (let* ((c-5 (mapcar #'list-length (mapcar (lambda (ind) (remove-if (lambda (val) (> 5 val))
									     ind))
						    population))))	     

					; rank individuals            
	    (if *debug*
		(progn (format t "~%Generation ~D: ~%Delta fitness = ~F~%Mutation Rate = ~F~%Count of 5+:~%0=~D  1=~D  2=~D  3=~D  4=~D  5=~D  6=~D  7=~D~%"
			       gen deltaFitness mutate-prob (count 0 c-5) (count 1 c-5) (count 2 c-5) (count 3 c-5) (count 4 c-5) (count 5 c-5)
			       (count 6 c-5) (count 7 c-5))
		       (funcall printer population fitnesses)))))
      
      ; #| SELECTION 1 
      ; choose half the population TWEAK ME!!!!!!!!!!
      (setf chosen (funcall selector (/ pop-size 2) population fitnesses))

      ; build up an offspring set to be the new population
      (while (< (list-length offspring) pop-size)
	(let ((parent1 (elt chosen (mod (incf i) (list-length chosen))))
	      (parent2 (elt chosen (random (list-length chosen)))))
	  (setf offspring (append offspring (funcall modifier parent1 parent2)))))

      ; evolve
      (setf population offspring)
      (setf fitnesses (mapcar evaluator population))
      (setf offspring nil))
    
    ; Final Statistics
    (setf bestIndex (position (apply #'max (first fitnesses) fitnesses) fitnesses))
    (format t "~%Best Fitness: ~F ~%Best Individual of Evolution: ~A"
	   (elt fitnesses bestIndex) (elt population bestIndex));  (setf *record* (elt fitnesses bestIndex)) (elt population bestIndex))
    
    ; return statement
    population))

;(evolve 50 100
; 	:setup #'float-vector-sum-setup
;	:creator #'float-vector-creator
;	:selector #'tournament-selector
;	:modifier #'float-vector-modifier
;       :Evaluator

;;;; Gp

;;; GP's tree individuals are considerably more complex to modify than
;;; simple vectors.  Get the GA system working right before tackling
;;; this part, trust me.

;; set up in the gp setup function -- for example, see
;; the code for gp-symbolic-regression-setup
(defparameter *nonterminal-set* nil)
(defparameter *terminal-set* nil)

;;; important hint: to use SETF to change the position of an element in a list
;;; or a tree, you need to pass into SETF an expression starting with the
;;; parent.  For example (setf (car parent) val) .... thus you HAVE to have
;;; access to the parent, not just the child.  This means that to store a
;;; "position", you have to store away the parent and the arg position of
;;; child, not the child itself.

(defun make-queue ()
  "Makes a random-queue"
  (make-array '(0) :adjustable t :fill-pointer t))
(defun enqueue (elt queue)
  "Enqueues an element in the random-queue"
  (progn (vector-push-extend elt queue) queue))
(defun queue-empty-p (queue)
  "Returns t if random-queue is empty"
  (= (length queue) 0))
(defun random-dequeue (queue)
  "Picks a random element in queue and removes and returns it.
Error generated if the queue is empty."
 ; (break)
  (let ((index (random (length queue))))
    (swap (elt queue index) (elt queue (1- (length queue))))
  ;  (break)
    (vector-pop queue)))

(defun range (size)
  (let ((count -1))
    (mapcar (lambda (el) (incf count))
	    (make-sequence 'list size))))

(defun build-node (non-terminal)
  "Given a non-terminal node of form (func argc), returns a quote resembling the invocation of func with argc fresh symbols"
  (apply #'list (first non-terminal) (mapcar (lambda (dum) (gensym)) (make-sequence 'list (second non-terminal)))))

(defun random-terminal ()
  "Returns a random element from the terminal set."
  (random-elt *terminal-set*))

(defun random-non-terminal ()
  "Returns a subtree built from random element from the non-terminal set."
  (build-node (random-elt *nonterminal-set*)))

(defun enqueue-args (node queue)
  "enqueues the arguments in node invocation list returns nil"
  (dolist (sym (rest node)) (enqueue sym queue)))

#|
  The simple version of PTC2 you will implement is as follows:

  PTC2(size):
  if size = 1, return a random terminal
  else
     q <- make-queue
     root <- random nonterminal
     count <- 1
     enqueue into q each child argument slot of root
     Loop until count + size_of_q >= size
        remove a random argument slot s from q
        a <- random nonterminal
        count <- count + 1
        fill the slot s with a
        enqueue into q each child argument slot of a
     Loop until size_of_q = 0
        remove a random argument slot s from q
        a <- random terminal
        fill the slot s with a
     return root

  Note that "terminals" will all be considered to be
  zero-argument functions.  Thus PTC might generate the
  s-expression tree:

  (cos (+ (x) (- (x) (x)) (sin (x))))

  but it should NOT generate the tree:

  (cos (+ x (- x x) (sin x)))


  Note that this has some gotchas: the big gotcha is that you have to keep track of
  argument slots in lisp s-expressions, and not just pointers to the values presently
  in those slots.  If you are totally lost as to how to implement that, I can provide
  some hints, but you should try to figure it out on your own if you can.
|#

(defun ptc2 (size)
  "If size=1, just returns a random terminal.  Else builds and
returns a tree by repeatedly extending the tree horizon with
nonterminals until the total number of nonterminals in the tree,
plus the number of unfilled slots in the horizon, is >= size.
Then fills the remaining slots in the horizon with terminals.
Terminals like X should be added to the tree
in function form (X) rather than just X."
  (if (equalp size 1) (random-terminal)
      (let ((q (make-queue))
	    (root (random-non-terminal))
	    (count 1)
	    tmp)
	(enqueue-args root q)
	;;;;;;;;;;;;;;;;;TODO
	(while (>= (+ count (length q)) size) '()
	  (incf count)
	  (setf tmp (random-non-terminal))
	  (setf (random-dequeue q) tmp)
	  (enqueue-args tmp q))	
	(while (not (queue-empty-p (print q))) root
	  (let ((slot (random-dequeue q)))
	    (setf slot (random-terminal)))))))

(defun gp-creator (&optional (size-limit *size-limit*))
   "Picks a random number within size-limit, then uses ptc2 to create
a tree of that size"
  (ptc2 (random size-limit)))

;;; GP TREE MODIFICATION CODE

(defun num-nodes (tree)
  "Returns the number of nodes in tree, including the root"
  (apply #'+ (length (remove-if #'listp tree)) (mapcar #'num-nodes (remove-if-not #'listp tree))))

(defun make-counter ()
  "returns a function that returns false until it has been called countdown times"
  (let ((steps (gensym)))
    (setf steps 0)
    (lambda (end)
      (equalp (incf steps) end))))

(defun nth-subtree (tree n)
    "Given a tree, finds the nth node by depth-first search though
the tree, not including the root node of the tree (0-indexed). If the
nth node is NODE, let the parent node of NODE is PARENT,
and NODE is the ith child of PARENT (starting with 0),
then return a list of the form (PARENT i).  For example, in
the tree (a (b c d) (f (g (h) i) j)), let's say that (g (h) i)
is the chosen node.  Then we return ((f (g (h) i) j) 0).
p
If n is bigger than the number of nodes in the tree
 (not including the root), then we return n - nodes_in_tree
 (except for root)."
  (let ((counter (make-counter)))
    (labels ((recurse (root)
	       (if (funcall counter n) (return-from nth-subtree root))
	       (mapcar (lambda (subtree)
			 (if (listp subtree)
			     (recurse subtree)
			     (if (funcall counter n)
				 (return-from nth-subtree subtree))))
		       (rest root))))
	     (recurse tree))))

(defun nth-subtree-parent (tree n)
  ;;; this is best described with an example:
  ;    (dotimes (x 12)
  ;           (print (nth-subtree-parent
  ;                      '(a (b c) (d e (f (g h i j)) k))
  ;                        x)))
  ;;; result:
  ;((A (B C) (D E (F (G H I J)) K)) 0)
  ;((B C) 0)
  ;((A (B C) (D E (F (G H I J)) K)) 1)
  ;((D E (F (G H I J)) K) 0)
  ;((D E (F (G H I J)) K) 1)
  ;((F (G H I J)) 0)
  ;((G H I J) 0)
  ;((G H I J) 1)
  ;((G H I J) 2)
  ;((D E (F (G H I J)) K) 2)
  ;0
  ;1
  ;NIL

    ;;; IMPLEMENT ME
  )

(defparameter *mutation-size-limit* 10)  

(defun random-subtree (ind)
  "Returns a random strict subtree (cannot be root) of the given individual"
  (subtree ind (random (num-nodes ind))))

(defun max-depth (root)
  "given a tree, calculates the maximum depth of the tree where (max-depth (a))=0"
  (apply #'max (mapcar (lambda (node) (if (listp node) (1+ (max-depth node)) 1))
		       (rest root))))

;(defun depth (root targetNode)
;   "Given a tree and a node within that tree, calculates the depth of the node within the tree,
; where (depth root root) -> 0"
;   (labels ((recurse (subtree level)
; 	     (mapcar (lambda (node)
; 		       (if (equalp node targetNode) (return-from depth level)
; 			   (if (listp node) (recurse node (1+ level)))))
; 		     (rest subtree))))
;     (recurse root 0)))

(defun depth (root targetNode)
  "Given a tree and a node within that tree, calculates the depth of the node within the tree,
# where (depth root root) -> 0" 
  (labels ((recurse (subtree level)                                         
 	     (mapcar (lambda (node)                                          
		       (if (equalp node targetNode) (return-from depth level)
 			   (if (listp node) (recurse node (1+ level)))))
 		     (rest subtree))))
    (recurse root 0)))
 
(defun subtree-mutation (ind &key (restrict-size *restrict-size*) (max-size *size-limit*) (mutate-size-limit *mutation-size-limit*))
  "Randomly selects a subtree of ind, determines its maximum depth,
and replaces it with a new tree, perhaps restricting its size"
  (if (not restrict-size)
      (setf (random-subtree ind) (ptc2 mutate-size-limit))
      (let* ((full-height (max-depth ind))
	     (n (random (num-nodes ind)))
	     (new-subtree-depth (- max-size (depth ind (subtree ind n)))))
	     (setf (subtree ind n) (ptc2 new-subtree-depth)))))

(defun gp-modifier (ind1 ind2)
  "Flips a coin.  If it's heads, then ind1 and ind2 are
crossed over using subtree crossover.  If it's tails, then
ind1 and ind2 are each mutated using subtree mutation, where
the size of the newly-generated subtrees is picked at random
from 1 to 10 inclusive.  Doesn't damage ind1 or ind2.  Returns
the two modified versions as a list."
 (if (random?)
  (progn
    (swap (random-subtree ind1) (random-subtree ind2))
    (list ind1 ind2))
  (list (subtree-mutation ind1) (subtree-mutation ind2))))

;;; SYMBOLIC REGRESSION
;;; This problem domain is similar, more or less, to the GP example in
;;; the lecture notes.  Your goal is to make a symbolic expression which
;;; represents a mathematical function consisting of SIN COS, EXP,
;;; +, -, *, and % (a version of / which doesn't give an error on
;;; divide-by-zero).  And also the function X, which returns a current
;;; value for the X variable.
;;;
;;; In symbolic regression, we generate 20 (x,y) pairs produced at
;;; random which fit the expression y = x^4 + x^3 + x^2 + x.  You can
;;; make up another function is you like, but that's the one we're going
;;; with here.  Using just these data pairs, the GP system will attempt
;;; to ascertain the function.  It will generate possible expressions
;;; as its individuals, and the fitness of an expression is how closely,
;;; for each X value, it gives the correct corresponding Y value.
;;;
;;; This is called SYMBOLIC regression because we're actually learning
;;; the mathematical expression itself, including transcendental functions
;;; like SIN and COS and E^.  As opposed to statistical linear or
;;; quadratic curve-fitting regressions which just try to learn the
;;; linear or quadratic parameters etc.
;;;
;;; An example 100% optimal solution:
;;;
;;; (+ (* (x) (* (+ (x) (* (x) (x))) (x))) (* (+ (x) (cos (- (x) (x)))) (x)))

;;; GP SYMBOLIC REGRESSION SETUP
;;; (I provide this for you)

(defun gp-symbolic-regression-setup ()
  "Defines the function sets, and sets up vals"

  (setq *nonterminal-set* '((+ 2) (- 2) (* 2) (% 2) (sin 1) (cos 1) (exp 1)))
  (setq *terminal-set* '(x))

  (setq *vals* nil)
  (dotimes (v *num-vals*)
    (push (1- (random 2.0)) *vals*)))

(defun poly-to-learn (x) (+ (* x x x x) (* x x x) (* x x) x))

;; define the function set
(defun x () *x*)
(defun % (x y) (if (= y 0) 0 (/ x y)))  ;; "protected division"
;;; the rest of the functions are standard Lisp functions

;;; GP SYMBOLIC REGRESSION EVALUATION

(defun gp-symbolic-regression-evaluator (ind)
  "Evaluates an individual by setting *x* to each of the
elements in *vals* in turn, then running the individual and
get the output minus (poly-to-learn *x*).  Take the
absolute value of the this difference.  The sum of all such
absolute values over all *vals* is the 'raw-fitness' Z.  From
this we compute the individual's fitness as 1 / (1 + z) -- thus
large values of Z are low fitness.  Return the final
individual's fitness.  During evaluation, the expressions
evaluated may overflow or underflow, or produce NaN.  Handle all
such math errors by
returning most-positive-fixnum as the output of that expression."
  ;;; hint:
  ;;; (handler-case
  ;;;  ....
  ;;;  (error (condition)
  ;;;     (format t "~%Warning, ~a" condition) most-positive-fixnum))

  ;;; IMPLEMENT ME

  )

;;; Example run
#|
(evolve 50 500
 	:setup #'gp-symbolic-regression-setup
	:creator #'gp-creator
	:selector #'tournament-selector
	:modifier #'gp-modifier
        :evaluator #'gp-symbolic-regression-evaluator
	:printer #'simple-printer
        :mutate-prob *boolean-mutation-probability*))
|#

;;; GP ARTIFICIAL ANT CODE
;;; for this part you'll need to implement both the evaluator AND
;;; make up the function that form the function set.

;;; In the artificial ant problem domain, you'll be evolving an s-expression
;;; which moves an ant around a toroidal map shown below.  The ant starts out
;;; at (0,0), facing east (to the right).  The functions in
;;; the expression are:
;;; (if-food-ahead --then-- --else--)   If food is directly ahead of the ant,
;;;                                     then evaluate the THEN expression, else
;;;                                     evaluate the ELSE expression
;;; (progn2 --item1-- --item2--)        Evaluate item1, then evaluate item 2
;;; (progn3 --item1-- --item2-- --item3--)  Evaluate item1, then item2, then item3
;;; (move)                              Move forward one unit
;;;                                     If you pass over a food pellet, it is eaten
;;;                                     and removed from the map.
;;; (left)                              Turn left
;;; (right)                             Turn right
;;;
;;;
;;; the way a tree is evaluated is as follows.  The whole tree is evaluated,
;;; and the functions move the ant about.  If the ant has not made a total of
;;; 600 MOVE, LEFT, and RIGHT operations yet, then the tree is evaluated AGAIN
;;; moving the ant some more from its current position.  This goes on until
;;; 600 operations have been completed, at which time the ant will not move
;;; any more.  If 600 operations are completed in the middle of the evaluation
;;; of a tree, the simplest approach is to have the MOVE command simply
;;; "stop working" so the ant doesn't gobble up any more pellets accidentally.

;;; The fitness of the artificial ant is the number of pellets it ate in the
;;; 600-operation period.  Maps are reset between evaluations of different
;;; individuals of course.

;;; Here's an optimal ant program (there are many such):
;;  (progn3 (if-food-ahead (move) (progn2 (left) (progn2 (left)
;;             (if-food-ahead (move) (right))))) (move) (right)))

;;; This is a hard problem for GP and you may need to run many times before you
;;; get a 100% perfect answer.

;;; Note that in my thesis it says 400 moves and not 600.  We're going with
;;; 600 here.  It's easier.


;;; some useful functions for you

(defun make-map (lis)
  "Makes a map out of a string-list such as *MAP-STRS*"
  (let ((map (make-array (list (length (first lis)) (length lis)))))
    (dotimes (y (length lis) map)
      (dotimes (x (length (elt lis y)))
	(setf (aref map x y)
	      (cond ((equalp #\# (elt (elt lis y) x)) nil)
		    (t t)))))))

(defparameter *map* (make-map *map-strs*) "The ant's map")


(defun direction-to-arrow (dir)
  "Returns a character which represents a given direction -- might
be useful for showing the movement along a path perhaps..."
  (cond ((= dir *n*) #\^)
	((= dir *s*) #\v)
	((= dir *e*) #\>)
	(t #\<)))

(defun maparray (function array &optional (same-type nil))
  "Maps function over array in its major order.  If SAME-TYPE,
then the new array will have the same element type as the old
array; but if a function returns an invalid element then an error
may occur.  If SAME-TYPE is NIL, then the array will accommodate
any type."
  (let ((new-array (apply #'make-array (array-dimensions array)
			  :element-type (if same-type
					    (array-element-type array)
					  t)
			  :adjustable (adjustable-array-p array)
			  (if (vectorp array)
			      `(:fill-pointer ,(fill-pointer array))
			    nil))))
    (dotimes (x (array-total-size array) new-array)
      (setf (row-major-elt new-array x)
	    (funcall function (row-major-aref array x))))))

(defun print-map (map)
  "Prints a map, which must be a 2D array.  If a value in the map
is T (indicating a space), then a '.' is printed.  If a value in the map
is NIL (indicating a food pellet), then a '#' is printed.  If a value in
the map is anything else, then it is simply PRINTed.  This allows you to
consider spaces to be all sorts of stuff in case you'd like to print a
trail of spaces on the map for example.  Returns NIL."
  (let ((dim (array-dimensions map)))
    (dotimes (y (second dim) nil)
      (format t "~%")
      (dotimes (x (first dim))
	(format t "~a"
		(let ((v (aref map x y)))
		  (cond ((equal v t) #\.)
			((null v) #\#)
			(t v))))))))


;; The four directions.  For relative direction, you might
;; assume that the ant always PERCEIVES things as if it were
;; facing north.

(defmacro absolute-direction (relative-dir ant-dir)
  "If the ant is facing ANT-DIR, then converts the perceived
RELATIVE-DIR direction into an absolute ('true') direction
and returns that."
  `(mod (+ ,relative-dir ,ant-dir) 4))

(defmacro x-pos-at (x-pos absolute-dir &optional (steps 1))
  "Returns the new x position if one moved STEPS steps the absolute-dir
direction from the given x position.  Toroidal."
  `(mod (cond ((= (mod ,absolute-dir 2) *n*) ,x-pos)         ;; n or s
	      ((= ,absolute-dir *e*) (+ ,x-pos ,steps))     ;; e
	      (t (+ ,x-pos (- ,steps) *map-width*)))         ;; w
	*map-width*))

(defmacro y-pos-at (y-pos absolute-dir &optional (steps 1))
  "Returns the new y position if onee moved STEPS steps in the absolute-dir
direction from the given y position.  Toroidal."
  `(mod (cond ((= (mod ,absolute-dir 2) *e*) ,y-pos)        ;; e or w
	      ((= ,absolute-dir *s*) (+ ,y-pos ,steps))     ;; s
	      (t (+ ,y-pos (- ,steps) *map-height*)))       ;; n
	*map-height*))


;;; the function set you have to implement
(defmacro if-food-ahead (then else)
  "If there is food directly ahead of the ant, then THEN is evaluated,
else ELSE is evaluated"
  ;; because this is an if/then statement, it MUST be implemented as a macro.
  `(if (food-p) ,then ,else))

(defun progn2 (arg1 arg2)
    "Evaluates arg1 and arg2 in succession, then returns the value of arg2"
    (declaim (ignore arg1))
    arg2)  ;; ...though in artificial ant, the return value isn't used ...

(defun progn3 (arg1 arg2 arg3)
  "Evaluates arg1, arg2, and arg3 in succession, then returns the value of arg3"
  (declaim (ignore arg1 arg2))
  arg3)  ;; ...though in artificial ant, the return value isn't used ...

(defun move ()
  "If the move count does not exceed *num-moves*, increments the move count
and moves the ant forward, consuming any pellet under the new square where the
ant is now.  Perhaps it might be nice to leave a little trail in the map showing
where the ant had gone."

(print "inside of function")
(if (<= *current-move* *num-moves*)
  (progn
  (print "inside of moves")
  (setf *current-move* (+ *current-move* 1))
  (if (= *current-ant-dir* 0)
    (progn
    (print "moving left")
    (setf *current-y-pos* (- *current-y-pos* 1))))
  (if (= *current-ant-dir* 1)
    (progn
    (print "moving right")
    (setf *current-y-pos* (+ *current-y-pos* 1))))
  (if (= *current-ant-dir* 2)
    (progn
    (print "moving up")
    (setf *current-x-pos* (+ *current-x-pos* 1))))
  (if (= *current-ant-dir* 3)
    (progn
    (print "moving down")
    (setf *current-x-pos* (- *current-x-pos* 1))))))
(if (equal "#" (subseq (elt *map-strs-copy* *current-x-pos*) *current-y-pos* (+ (- (length (elt *map-strs-copy* *current-x-pos*)) (length (subseq (elt *map-strs-copy* *current-x-pos*) *current-y-pos*))) 1)))
    (progn
    (setf *map-str-copy* (substitute (concatenate 'string (subseq (elt *map-strs-copy* *current-x-pos*) 0 *current-y-pos*) (replace (subseq (elt *map-strs-copy* *current-x-pos*) *current-y-pos* (+ *current-y-pos* 1)) "-") (subseq (elt *map-strs-copy* *current-x-pos*) (+ *current-y-pos* 1) (- (length (elt *map-strs-copy* *current-x-pos*)) 1))) (elt *map-strs-copy* *current-x-pos*) *map-strs-copy*))
    (setf *eaten-pellets* (+ *eaten-pellets* 1)))))


(defun left ()
  "Increments the move count, and turns the ant left"

  (if (<= *current-move* *num-moves*)
    (progn
    (setf *current-move* (+ *current-move* 1))
    (if (= *current-ant-dir* 0)
      (setf *current-ant-dir* 3)
      (if (= *current-ant-dir* 1)
        (setf *current-ant-dir* 2)
        (if (= *current-ant-dir* 2)
          (setf *current-ant-dir* 0)
          (if (= *current-ant-dir* 3)
            (setf *current-ant-dir* 1))))))))

(defun right ()
  "Increments the move count, and turns the ant right"
  (if (<= *current-move* *num-moves*)
    (progn
    (setf *current-move* (+ *current-move* 1))
    (if (= *current-ant-dir* 0)
      (setf *current-ant-dir* 2)
      (if (= *current-ant-dir* 1)
        (setf *current-ant-dir* 3)
        (if (= *current-ant-dir* 2)
          (setf *current-ant-dir* 1)
          (if (= *current-ant-dir* 3)
            (setf *current-ant-dir* 0))))))))

;; I provide this for you
(defun gp-artificial-ant-setup ()
  "Sets up vals"
  (setq *nonterminal-set* '((if-food-ahead 2) (progn2 2) (progn3 3)))
  (setq *terminal-set* '(left right move))
  (setq *map* (make-map *map-strs*))
  (setq *current-move* 0)
  (setq *eaten-pellets* 0)
  )

;; you'll need to implement this as well

(defun gp-artificial-ant-evaluator (ind)
  "Evaluates an individual by putting it in a fresh map and letting it run
for *num-moves* moves.  The fitness is the number of pellets eaten -- thus
more pellets, higher (better) fitness."
  (setf *map-str-copy* (copy-seq *map-strs*))
  (setf *eaten-pellets* 0)
  (dotimes (number *num-moves* *eaten-pellets*)
    (eval ind)))

;; you might choose to write your own printer, which prints out the best
;; individual's map.  But it's not required.

#|
(evolve 50 500
 	:setup #'gp-artificial-ant-setup
	:creator #'gp-creator
	:selector #'tournament-selector
	:modifier #'gp-modifier
        :evaluator #'gp-artificial-ant-evaluator
	:printer #'simple-printer)
|#

