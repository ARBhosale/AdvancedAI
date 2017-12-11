;;;;;;;; SIMPLE-PLAN
;;;;;;;; The following planner is a brute-force planning partial-order (POP) system.  
;;;;;;;; It doesn't use a heuristic, but instead just uses iterative-deepening search.  
;;;;;;;; If you want to see a high-quality, free POP planner, check out UCPOP at
;;;;;;;; https://www.cs.washington.edu/ai/ucpop.html
;;;;;;;; Note that there are many better planners still at this point (POP is getting old).
;;;;;;;;
;;;;;;;; The following planner does not use variables -- it's propositional and not
;;;;;;;; predicate-logic based.  Because it doesn't use
;;;;;;;; variables, we have to write more code to describe a problem (see the Blocks World
;;;;;;;; example at end) but it is a much easier algorithm to for you to write (you don't have to
;;;;;;;; be involved in unification.  Happy!).  
;;;;;;;;
;;;;;;;; I am giving you some basic code which defines predicates, links,
;;;;;;;; orderings, and strips operators and plans.  Then I'm giving you
;;;;;;;; the entry code which creates a minimal plan.  Lastly, you get a
;;;;;;;; simple two-block blocks world problem to play with, plus a three-
;;;;;;;; block blocks world problem to play with after you get the two-blocks
;;;;;;;; version working properly.
;;;;;;;;
;;;;;;;; SOME HINTS:
;;;;;;;; 1. Read up on DOTTED PAIRS
;;;;;;;; 2. Read up on ASSOCIATION LISTS
;;;;;;;; 3. Read up on STRUCTURES
;;;;;;;; 4. Read up on RETURN-FROM, RETURN, CATCH, and THROW
;;;;;;;; 5. MAPC and other mapping functions might be useful to you.
;;;;;;;; 6. So might HASH TABLES
;;;;;;;;
;;;;;;;; This is a tough assignment.  If you have any questions, feel free to ask me.
;;;;;;;; If you get really stuck, I might be willing to "release" a function or two
;;;;;;;; to you, but at a cost in project grade of course.  Still, it'd be better than
;;;;;;;; not getting the project running.
;;;;;;;;
;;;;;;;; The big challenge in this project is getting the code running fast.  The class
;;;;;;;; will likely have a *huge* variance in running speed.  I can implement this code
;;;;;;;; to run very fast indeed, just a few milliseconds, so if your code is taking
;;;;;;;; many seconds to run, it's time to think about optimization and algorithmic
;;;;;;;; improvements.  
;;;;;;;;
;;;;;;;; Once you get the code working you might then think about how to implement some
;;;;;;;; other problems.  Check out ones in the book and think about how to propositionalize
;;;;;;;; them.  Or invent some fun problems.  You'll discover quickly that variables help
;;;;;;;; a lot!  A fun project might be to write a bit of code which converts a variable-style
;;;;;;;; problems to propositionalized ones so you don't have to write a million operators.
;;;;;;;; Or you might test how the system scales with more complex problems.  At any rate,
;;;;;;;; do some interesting extension of it.
;;;;;;;;
;;;;;;;; Provide the code for the project and a report as usual describing what you did and
;;;;;;;; what extensions or experiments you performed.  Please do not deviate far from the
;;;;;;;; code proper -- it's hard to grade otherwise.


;;;;; PREDICATES

;;; A predicate is a list of the form (t-or-nil name)
;;; where the t-or-nil indicates if it's negated,
;;; and NAME is a symbol indicating the predicate name.
;;; Example: (NIL B-ON-A)  "B is not on A"

(defun negate (predicate)
  "Negates a predicate.  Pretty simple!"
  (cons (not (first predicate)) (rest predicate)))


;;;;;; STRIPS OPERATORS
;;;;;; A strips operator has is described below.  Note that
;;;;;; UNIQ allows two operators with the same name, preconds
;;;;;; and effects to be in the plan at once.

(defstruct operator
   "Defines a strips operator consisting of
a NAME (a symbol or string),
a UNIQ gensym symbol assigned when the operator is added to the plan,
a list of PRECONDITIONS (predicates)
a list of EFFECTS ( predicates),

The resultant function MAKE-OPERATOR creates a *template*,
which is different from an instantiated operator actually in a plan.
Use instantiate-operator to create an operator from a template."
  name uniq preconditions effects)


;; Expect a possible warning here about redefinition
(defun are-same-operators (operator1 operator2)
    (if (equalp (operator-uniq operator1) (operator-uniq operator2))
        t
        nil
    )
)

(defun copy-operator (operator)
  "Copies the operator and assigns it a new unique gensym symbol to make
it unique as far as EQUALP is concerned.  Returns the copy."
  ;; I suggest you use this code to guarantee that the operator is properly
  ;; copied out of the templates.
  (let ((op (copy-structure operator)))
    (setf (operator-uniq op) (gensym))
    op))



;;;;;;; LINKS
;;;;;;; A link is a structure that specifies a causal link with a from-operator,
;;;;;;; a to-operator, and precondition of the to-operator involved
;;;;;;; (which is the SAME as the effect of the from-operator!)

(defstruct (link
	        (:print-function print-link))
  "FROM and TO are operators in the plan.
  PRECOND is the predicate that FROM's effect makes true in TO's precondition."
  from precond to)

(defun print-link (p stream depth)
  "Helper function to print link in a pretty way"
  (declare (ignorable depth))
  (format stream "#< (~a)~a -> (~a)~a : ~a >"
	    (when (link-from p) (operator-uniq (link-from p)))
	      (when (link-from p) (operator-name (link-from p)))
	        (when (link-to p) (operator-uniq (link-to p)))
		  (when (link-to p) (operator-name (link-to p)))
		    (link-precond p)))


;;;;;;; ORDERINGS
;;;;;;; An ordering is just a dotted pair of the form (before-op . after-op)
;;;;;;; where before-op and after-op are strips operators (instances of
;;;;;;; the OPERATOR structure).  The ordering specifies
;;;;;;; that before-op must come before after-op.


(defun print-ordering (p stream depth)
  "Helper function to print link in a pretty way"
  (declare (ignorable depth))
  (format stream "#[ (~a)~a -> (~a)~a ]"
	    (operator-uniq (first p))
	      (operator-name (first p))
	        (operator-uniq (rest p))
		  (operator-name (rest p))))


;;;;;;; PLANS
;;;;;;; A plan is a list of operators, a list of orderings, and a list of
;;;;;;; links, plus the goal and start operator (which are also in the operator
;;;;;;; list).

(defstruct (plan (:print-function print-plan))
  "A collection of lists of operators, orderings, and links,
plus a pointer to the start operator and to the goal operator."
  operators orderings links start goal)

(defun print-plan (p stream depth)
  "Helper function print plan in a pretty way"
  (declare (ignorable depth))
  (format stream "#< PLAN operators: ~{~%~a~} ~%links: ~{~%~a~} ~%orderings: ~{~%~a~}~%>"
	    (plan-operators p) (plan-links p)
	      (mapcar #'(lambda (ordering)
			        (print-ordering ordering nil 0))
		        (plan-orderings p))))

;; Expect a possible warning here about redefinition
(defun copy-plan (plan)
  ;; I suggest you use this code to guarantee that the plan is copied
  ;; before you do any destructive coding on it.
  "Deep-copies the plan, and copies the operators, orderings, and links."
  (let ((p (copy-structure plan)))
    (setf (plan-operators p) (copy-tree (plan-operators p)))
    (setf (plan-orderings p) (copy-tree (plan-orderings p)))
    (setf (plan-links p) (copy-tree (plan-links p)))
    p))




;;;;;;;;; UTILITY FUNCTIONS
;;;;;;;;; I predict you will find these functions useful.

;;;; Reachable takes an association list and determines if you can reach
;;;; an item in the list from another item.  For example:
;;;;
;;;; (reachable '((a . b) (c . d) (b . c) (b . e) (e . a)) 'e 'd)
;;;; --> T   ;; e->a, a->b, b->c, c->d

(defun reachable (assoc-list from to)
  "Returns t if to is reachable from from in the association list."
  ;; expensive!

;;; SPEED HINT.  You might rewrite this function to be more efficient.
;;; You could try dividing the list into two lists, one consisting of association pairs
;;; known to be reachable from FROM and ones not know to be reachable, then
;;; using the property of transitivity, move pairs from the second list to the first
;;; list, until either you discover it's reachable, or nothing else is moving.

  (dolist (x assoc-list nil)
    (when (and (equalp (car x) from)
	              (or (equalp (cdr x) to)
			     (reachable (remove x assoc-list) (cdr x) to)))
      (return t))))


;;;; Cyclic-assoc-list takes an association list and determines if it
;;;; contains a cycle (two objects can reach each other)
;;;;
;;;; (cyclic-assoc-list '((a . b) (c . d) (b . c) (b . e) (e . a)))
;;;; --> T   ;; a->b, b->e, e->a
;;;;
;;;; (cyclic-assoc-list '((a . a)))
;;;; --> T   ;; a->a

(defun cyclic-assoc-list (assoc-list)
  (dolist (x assoc-list nil)
    (when (reachable assoc-list (cdr x) (car x))
      (return t))))

;;;; Binary-combinations returns all N^2 combinations of T and NIL.
;;;; 
;;;; (binary-combinations 4)
;;;; -->
;;;; ((NIL T NIL T) (T T NIL T)
;;;;  (NIL NIL NIL T) (T NIL NIL T)
;;;;  (NIL T T T) (T T T T)
;;;;  (NIL NIL T T) (T NIL T T)
;;;;  (NIL T NIL NIL) (T T NIL NIL)
;;;;  (NIL NIL NIL NIL) (T NIL NIL NIL)
;;;;  (NIL T T NIL) (T T T NIL)
;;;;  (NIL NIL T NIL) (T NIL T NIL))

(defun binary-combinations (n)
  "Gives all combinations of n t's and nils"
  (let ((bag '(())))
    (dotimes (x n bag)
      (let (bag2)
	(dolist (b bag)
	    (push (cons t b) bag2)
	      (push (cons nil b) bag2))
	(setf bag bag2)))))



;;;;;; PLANNING CODE TEMPLATES
;;;;;;
;;;;;; The following are the functions I used to implement my planner.
;;;;;; You have been given all interfaces I used, but no implementation.
;;;;;; This is how I went about doing it -- if you want to you can of course
;;;;;; do the code differently, but indicate that you are doing so.
;;;;;;
;;;;;; The recursion looks like this:
;;;;;; SELECT-SUBGOAL calls CHOOSE-OPERATOR, which calls HOOK-UP-OPERATOR,
;;;;;; which calls RESOLVE-THREATS, which in turn calls SELECT-SUBGOAL.
;;;;;; All of these functions return a either plan
;;;;;; (the solution) or NIL (failure to find a solution).
;;;;;; 
;;;;;; In SELECT-SUBGOAL I test to see if the maximum depth is exceeded
;;;;;; and fail immediately if it is.  That's the only place I check for
;;;;;; depth.  You are free to test other places if you want.  Then I
;;;;;; I increment the current depth before passing it to CHOOSE-OPERATOR.
;;;;;;
;;;;;; Some hints: I also used PUSH and SETF and DOLIST a lot,
;;;;;; as well as a healthy dose of MAPCAR, MAPC, and MAPL.  Also you might
;;;;;; want to read up on CONSes of the form (a . b) which I use a lot,
;;;;;; and also ASSOCIATION LISTS which are very convenient in certain spots


(defun before-p (operator1 operator2 plan)
  "Operator1 is ordered before operator2 in plan?"
;;; perhaps you have an existing function which could help here.
 (reachable (plan-orderings plan) (operator-name operator1) (operator-name operator2))     
 )



(defun link-exists-for-precondition-p (precond operator plan)
  "T if there's a link for the precond for a given operator, else nil.
precond is a predicate."
  
  (loop for mylink in (plan-links plan)
	do
	(if (equalp (operator-uniq operator) (operator-uniq (link-to mylink)))
	    ;; we found the link that goes to the operator
	    ;; Now, we check if the preconditions match
	    ;; The link selected is from an temp_operator to the operator
	    (if (equalp precond (link-precond mylink))
		(return-from link-exists-for-precondition-p t)
	      )	
	    )
	)
  nil 
  )


(defun operator-threatens-link-p (operator link plan)
  "T if operator threatens link in plan, because it's not ordered after
or before the link, and it's got an effect which counters the link's effect."
;;; SPEED HINT.  Test the easy tests before the more costly ones.

  (if (equalp (operator-uniq operator) (operator-uniq (link-from link)))
      (return-from operator-threatens-link-p nil)
    )
  (if (equalp (operator-uniq operator) (operator-uniq (link-to link)))
      (return-from operator-threatens-link-p nil)
    )
  (let* (
	 (pc (link-precond link)) ;; precondition of link 
	 (pc-not (negate pc))
	 )
    ;; if operator effect is equal to pc-not, that means it may threaten it.
    (loop for effect in (operator-effects operator)
	  do
	  (if (equalp effect pc-not)
	      ;; Now we check if the either operators on either side of link are reachable
	      ;; The operator may occur either before or after, so we test permutations of from and to
	      (if (or (reachable (plan-orderings plan) (operator-name operator) (operator-name (link-from link)))
		      (reachable (plan-orderings plan) (operator-name (link-to link)) (operator-name operator)))
		  (progn
		    ;; at least one operator on either side is reachable
		    (return-from operator-threatens-link-p nil)
		    )
		(progn
		  ;; None of the operators on either side are reachable
		  (return-from operator-threatens-link-p t)
		  )
		)
	    )
	  )
    ) 

  
    nil
)

(defun inconsistent-p (plan)
  "Plan orderings are inconsistent"
  ;; hint: cyclic-assoc-list
  (let ((orderings (plan-orderings plan)))
    (cyclic-assoc-list orderings)
 )
)

(defun pick-precond (plan)
  "Return ONE (operator . precondition) pair in the plan that has not been met yet.
If there is no such pair, return nil"
;; (format t "~%Picking an operator with an open pre-condition in plan:~a~%" plan)
    (dolist (operator-in-plan (plan-operators plan))
        (dolist (precondition (operator-preconditions operator-in-plan))
            (if precondition
                (if (not (link-exists-for-precondition-p precondition operator-in-plan plan))
                    (progn
                        ;; (format t "~%Found operator:~a ~% Open precondition:~a~%" operator-in-plan precondition)
                        (return-from pick-precond (cons operator-in-plan precondition))
                    )
                )
            )
        )
    )
    ;; (format t "Could not find any operator with open precondition.")
    nil
)

(defun all-effects (precondition plan)
  "Given a precondition, returns a list of ALL operators presently IN THE PLAN which have
effects which can achieve this precondition."
  ;; hint: there's short, efficient way to do this, and a long,
  ;; grotesquely inefficient way.  Don't do the inefficient way.
  (let ((operators '()))
    ;; (dolist (link-in-plan (plan-links plan))
    ;;     (if (equalp precondition (link-precond link-in-plan))
    ;;         (push (link-to link-in-plan) operators)
    ;;     )
    ;; )
    (dolist (operator (plan-operators plan))
        (if (operator-effects operator)
            (dolist (operator-effect (operator-effects operator))
                (if (equalp precondition operator-effect)
                    (push operator operators)
                )
            )
        )
    )
    operators
  )
)

(defun all-operators (precondition)
  "Given a precondition, returns all list of ALL operator templates which have
an effect that can achieve this precondition."
  ;; hint: there's short, efficient way to do this, and a long,
  ;; grotesquely inefficient way.  Don't do the inefficient way.
  (gethash precondition *operators-for-precond*)
)

(defun was-precond-pair-tried (precond-pair-list precond-pair)
    (if (member precond-pair precond-pair-list)
        t
        nil
    )
)

(defun select-subgoal (plan current-depth max-depth)
  "For all possible subgoals, recursively calls choose-operator
on those subgoals.  Returns a solved plan, else nil if not solved."
    ;;; an enterprising student noted that the book says you DON'T have
    ;;; to nondeterministically choose from among all preconditions --
    ;;; you just pick one arbitrarily and that's all.  Note that the
    ;;; algorithm says "pick a plan step...", rather than "CHOOSE a
    ;;; plan step....".  This makes the algorithm much faster.

    ;; checking if maximum depth reached
    ;; (format t "~%Selecting sub-goal for plan:~a~%" plan)
    (if (> current-depth max-depth)
        (progn
            (if (not (inconsistent-p plan))
                (progn
                    ;; (format t "~% Depth reached. Returning nil although we had a consistent plan: ~a~%" plan)
                    (return-from select-subgoal nil)
                )
                (progn
                    ;; (format t "~% Depth reached. Returning nil ")
                    (return-from select-subgoal nil)
                )
            )
        )
        (progn
            (let ((sub-goal (pick-precond plan)))
                ;; checking if sub-goal exists
                ;; (format t "~%Sub goal picked:~a~%" sub-goal)
                (if (not sub-goal)
                    (progn
                        ;; nil
                        ;; (format t "~% No sub goal ~%")
                        (return-from select-subgoal plan)
                    )
                )
                (incf current-depth)
                (choose-operator sub-goal plan current-depth max-depth)
            )
        )

    )
    
    
)


(defun choose-operator (op-precond-pair plan current-depth max-depth)
  "For a given (operator . precondition) pair, recursively call
hook-up-operator for all possible operators in the plan.  If that
doesn't work, recursively call add operators and call hook-up-operators
on them.  Returns a solved plan, else nil if not solved."

;;   (format t "~% Max Depth :~a~%" max-depth)

    (let ((effect-to-find (cdr op-precond-pair)) operators-with-this-effect)
        ;; (format t "~% Finding operators with effect:~a~%" effect-to-find)

	;;checking for an operator already in plan
        
        (setf operators-with-this-effect (all-effects effect-to-find plan))
        (dolist (operator operators-with-this-effect)
            (let (temp-for-plan)
                ;; (format t "~%Checking for an operator already in plan~%")
                (setf temp-for-plan (hook-up-operator operator (car op-precond-pair) effect-to-find plan current-depth max-depth nil))
                (if temp-for-plan
                    (progn
                        ;; (format t "~%Solved plan found using operator in plan. Plan:~a~%" temp-for-plan)
                        (return-from choose-operator temp-for-plan)
                    )
                    ;; (progn
                    ;;     (if (> current-depth max-depth)
                    ;;         (return-from choose-operator nil)
                    ;;     )
                    ;; )
                )
            )
        )

        ;if there is no solved plan found, checking for an operator from all operators
        
            (progn
                ;; (format t "~%Current depth:~a:~% Max-depth:~a~%" current-depth max-depth)
                ;; (format t "~%Checking for an operator from all operators~%")
                (setf operators-with-this-effect (all-operators effect-to-find))
                ;; (format t "~%All operators having effect~a~%~%Operators:~a~%" effect-to-find operators-with-this-effect)
                (dolist (operator operators-with-this-effect)
                    (let (temp-for-plan temp-operator)
                        (setf temp-operator (copy-operator operator))
                        (setf temp-for-plan (add-operator temp-operator plan))
                        (setf temp-for-plan (hook-up-operator temp-operator (car op-precond-pair) effect-to-find temp-for-plan current-depth max-depth t))
                        (if temp-for-plan
                            (progn
                                ;; (format t "~%Solved plan found using all operators. Plan:~a~%" temp-for-plan)
                                (return-from choose-operator temp-for-plan)
                            )
                            ;; (progn
                            ;;     (if (> current-depth max-depth)
                            ;;         (return-from choose-operator nil)
                            ;;     )
                            ;; )
                        )
                    )
                )
            )   
        
        nil
    )
)

(defun add-operator (operator plan)
  "Given an OPERATOR and a PLAN makes a copy of the plan [the
operator should have already been copied out of its template at this point].
Then adds that copied operator
the copied plan, and hooks up the orderings so that the new operator is
after start and before goal.  Returns the modified copy of the plan."
  ;;; hint: make sure you copy the plan!
  ;;; also hint: use PUSHNEW to add stuff but not duplicates
  ;;; Don't use PUSHNEW everywhere instead of PUSH, just where it
  ;;; makes specific sense.
;;   (format t "~%Adding new operator ~a" (operator-uniq operator))
  (let ((new-plan (copy-plan plan)))
    (push operator (plan-operators new-plan))
    (let ((start (plan-start new-plan)) (goal (plan-goal new-plan)))
    ;;   (format t "~%Now Pushing ~a" (cons start (operator-name operator)))
    ;;   (format t "~%Now Pushing ~a" (cons (operator-name operator) goal))
      
        (pushnew (cons start operator) (plan-orderings new-plan))
        (pushnew (cons operator goal) (plan-orderings new-plan))
    )
    new-plan
  )
)

(defun hook-up-operator (from to precondition plan
			            current-depth max-depth
				          new-operator-was-added)
  "Hooks up an operator called FROM, adding the links and orderings to the operator
TO for the given PRECONDITION that FROM achieves for TO.  Then
recursively  calls resolve-threats to fix any problems.  Presumes that
PLAN is a copy that can be modified at will by HOOK-UP-OPERATOR. Returns a solved
plan, else nil if not solved."
  ;;; hint: want to go fast?  The first thing you should do is
  ;;; test to see if TO is already ordered before FROM and thus
  ;;; hooking them up would make the plan inconsistent from the get-go
  ;;; also hint: use PUSHNEW to add stuff but not duplicates  
  ;;; Don't use PUSHNEW everywhere instead of PUSH, just where it
  ;;; makes specific sense.

  ;;checking if TO is already ordered before FROM
;;   (format t "~%hook-up checking if TO is already ordered before FROM~%")
;;   (if (reachable (plan-orderings plan) from to)
;;     (progn
;;         (format t "~%This operator is reachable. ~%Plan:~a~%From:~a ~%To:~a~%Moving on.~%" plan from to)
;;         (return-from hook-up-operator nil)
;;     )
;;   )

;;   (format t "~%From: ~a" (operator-uniq from))
            
  
    (if new-operator-was-added
        (progn
            ;; (format t "~%Hooking up a new operator:~a~%" from)
            (let ((new-link (make-link :from from :precond precondition :to to)))
                (push new-link (plan-links plan))
                (if (not (are-same-operators to (plan-goal plan)))
                    (if (not (are-same-operators from (plan-start plan)))
                        (pushnew (cons from to) (plan-orderings plan))
                    )
                )
                (let ((threats-found (threats plan from new-link)))
                    (resolve-threats plan threats-found current-depth max-depth)
                )
            )    
        )
        (progn
            ;; (format t "~%Hooking up an exisitng plan operator:~a~%" from)
            (let ((new-link (make-link :from from :precond precondition :to to)))
                (push new-link (plan-links plan))
                (if (not (are-same-operators to (plan-goal plan)))
                    (if (not (are-same-operators from (plan-start plan)))
                        (pushnew (cons from to) (plan-orderings plan))
                    )
                )
                
                (let ((threats-found (threats plan nil new-link)))
                    (resolve-threats plan threats-found current-depth max-depth)
            )
        )   
    )
    )
  ;;
)

(defun threats (plan maybe-threatening-operator maybe-threatened-link)
  "After hooking up an operator, we have two places that we need to check for threats.
First, we need to see if the link we just created is threatened by some operator.
Second, IF we just added in an operator, then we need to check to see if it threatens
any links.

This function should return a list of (op . link) pairs (called ''threats'') which
indicate all the situations where some operator OP threatens a link LINK.  The only
situations you need to check are the ones described in the previous paragraph.

This function should assume that if MAYBE-THREATENING-OPERATOR is NIL, then no
operator was added and we don't have to check for its threats.  However, we must
always check for any operators which threaten MAYBE-THREATENED-LINK."

    (let ((threats-found '()))
    ;; (format t "~%Finding threats in plan:~a~%" threats-found)
        ;; 1. checking if new link is threatened by operators in the plan
        (dolist (operator-in-plan (plan-operators plan))
            (if (operator-threatens-link-p operator-in-plan maybe-threatened-link plan)
                (pushnew (cons operator-in-plan maybe-threatened-link) threats-found)
            )
        )

        ;; 2. checking if new operator threatens links in plan
        (if maybe-threatening-operator
            (progn
                (dolist (link-in-plan (plan-links plan))
                    (if (operator-threatens-link-p maybe-threatening-operator link-in-plan plan)
                        (pushnew (cons maybe-threatening-operator link-in-plan) threats-found)
                    )
                )
            )
        )
        ;; (format t "~%Threats in plan:~a~%" (list-length threats-found))
        threats-found
    )
)

(defun generate-promoted-demoted-plans (promote-demote-function threat plans new-plan)
    ;; (format t "~%PromoteDemote function:~a~% On plan:~a~%" promote-demote-function new-plan)
    (funcall promote-demote-function (car threat) (cdr threat) new-plan)
    ;; (format t "~%After promoteDemote function:~a~% On plan:~a~%" promote-demote-function new-plan)
    (setf plans (check-and-add-plan plans new-plan))
    ;; (format t "~%After checking consistency, Plans:~a~%" plans)
    plans
)

(defun generate-promoted-demoted-plan (promote-demote-function threat original-plan)
    (let (modified-plan)
        (setf modified-plan (funcall promote-demote-function (car threat) (cdr threat) original-plan))
        modified-plan
    )
)

(defun check-and-add-plan (plans plan)
    ;; (format t "are plans adding? :~a~%" plan)
    (if (not (inconsistent-p plan))
        (progn
            ;; (format t "~%Plan is consistent.~%")
            (push plan plans)
            ;; (format t "~%Adding ~%Plan:~a to Plans:~a~%" plan plans)
        )
        ;; (format t "~%Plan is not consistent~%")
        
    )
    plans
)

(defun get-similar-threat-in-new-plan (threat new-plan)
    (let (new-threat-op new-threat-to new-threat-from (new-threat-pre (link-precond (cdr threat))))
        (dolist (operator (plan-operators new-plan))
            (if (equalp (operator-name operator) (operator-name (car threat)))
                (setf new-threat-op operator)
            )
            (if (equalp (operator-name operator) (operator-name (link-from (cdr threat))))
                (setf new-threat-from operator)
            )
            (if (equalp (operator-name operator) (operator-name (link-to (cdr threat))))
                (setf new-threat-to operator)
            )
        )
        (cons new-threat-op (make-link :from new-threat-from :precond new-threat-pre :to new-threat-to))
    )
)

(defun all-promotion-demotion-plans (plan threats-found)
  "Returns plans for each combination of promotions and demotions
of the given threats, except  for the inconsistent plans.  These plans
are copies of the original plan."
  ;;; Hint: binary-combinations could be useful to you.
  ;;; Also check out MAPC
  ;;; SPEED HINT.  You might handle the one-threat case specially.
  ;;; In that case you could also check for inconsistency right then and there too.
  (if (not threats-found)
    (progn
        (let ((consistent-plans '()))
            (setf consistent-plans (check-and-add-plan consistent-plans plan))
            (return-from all-promotion-demotion-plans consistent-plans)
        )
    )
    
  )
;;   (format t "~%all-promotion-demotion-plans for threats found:~a~%" threats-found)
;;   (if (equalp 1 (list-length threats-found))
;;     (progn
;;         (let ((threat (car threats-found)) (consistent-plans '()))
;;             (let ((new-plan (copy-plan plan)))
;;             ;; (format t "are plans adding? :~a~%" consistent-plans)
;;             (generate-promoted-demoted-plans #'promote threat consistent-plans new-plan)
            
;;             (generate-promoted-demoted-plans #'demote threat consistent-plans new-plan)
;;             ;; (consistent-plans)
;;             (format t "one threat plans:~a~%" consistent-plans)
;;             (return-from all-promotion-demotion-plans consistent-plans)
;;         )
;;     )
;;     )
;;   )
;; (format t "~%all-promotion-demotion-plans threats:~a~%" threats-found)
  (let* ((number-of-threats (list-length threats-found)) (combinations (binary-combinations number-of-threats)) (consistent-plans '()))
    ;; (format t "are plans adding2? :~a~%" consistent-plans)
    (dolist (combination combinations)
        ;; (format t "Combination for threat/s:~% ~a~%" combination)
        (let ((updated-plan (copy-plan plan)))
            (mapc #'(lambda (threat is-promote) 
                ;; (format t "~%Inside combination lambda. ~%Threat: ~a ~% isPromote:~a~%" threat is-promote)
                
                (if is-promote
                    (setf updated-plan (generate-promoted-demoted-plan #'promote (get-similar-threat-in-new-plan threat updated-plan) updated-plan))
                    (setf updated-plan (generate-promoted-demoted-plan #'demote (get-similar-threat-in-new-plan threat updated-plan) updated-plan))
                )
            ) threats-found combination)
            (setf consistent-plans (check-and-add-plan consistent-plans updated-plan))
        )
    )
    consistent-plans  
    )
  
)

(defun promote (operator link plan)
  "Promotes an operator relative to a link.  Doesn't copy the plan."
;;   (format t "~%Promoting plan:~%~a" plan)
;;   (format t "On Operator:~a~%" (operator-uniq operator))
  
  (let ((to-operator-in-link (link-to link))
	(from-operator-in-link (link-from link)))
    ;; (format t "~%Now Pushing from promote :~a"  (cons operator from-operator-in-link))
    (pushnew (cons operator from-operator-in-link) (plan-orderings plan))
    (pushnew (cons operator to-operator-in-link) (plan-orderings plan))
    ;; (format t "~%Promoted plan:~%~a" plan)
    plan
  )
)

(defun demote (operator link plan)
  "Demotes an operator relative to a link.  Doesn't copy the plan."
;;   (format t "~%Demoting plan~%")
;;   (format t "On Operator:~a~%" (operator-uniq operator))
;;   (let ((to-operator-in-link (link-to link)))
;;     (pushnew (cons to-operator-in-link operator) (plan-orderings plan))
;;     plan
;;   )

  (let ((to-operator-in-link (link-to link))
	(from-operator-in-link (link-from link)))
    ;; (format t "~%Now Pushing from demote :~a" (cons from-operator-in-link operator))
    ;; (format t "~%Now Pushing from demote :~a" (cons operator to-operator-in-link))
    (pushnew (cons from-operator-in-link operator) (plan-orderings plan))
    (pushnew (cons to-operator-in-link operator) (plan-orderings plan))
    ;; (format t "~%Demoted plan:~%~a" plan)
    plan
  )
)

(defun resolve-threats (plan threats-found current-depth max-depth)
  "Tries all combinations of solutions to all the threats in the plan,
then recursively calls SELECT-SUBGOAL on them until one returns a
solved plan.  Returns the solved plan, else nil if no solved plan."
;; (format t "~%Resolving threats:~a ~% for plan:~a~%" threats-found plan)
    (let ((consistent-plans (all-promotion-demotion-plans plan threats-found)) (solved-plan nil))
        (if (not consistent-plans)
            (progn
                (return-from resolve-threats nil)
            )
        )
        ;; (format t "~%Found some consistent prodem plans:~a~%" consistent-plans)
        (dolist (consistent-plan consistent-plans)
            (setf solved-plan (select-subgoal consistent-plan current-depth max-depth))
            (if solved-plan
                (progn
                    ;; (format t "~%Found a solved-plan for a consistent plan!!~%")
                    (return-from resolve-threats solved-plan)
                )
                (progn
                    (decf current-depth)
                )
            )
        )
        nil
    )
)




;;;;;;; DO-POP
;;;;;;; This is the high-level code.  Note it creates a goal and a start
;;;;;;; operator, then creates a plan with those operators and an ordering
;;;;;;; between them.  Then it does iterative-deepening, calling
;;;;;;; SELECT-SUBGOAL with ever-larger maximum depths.  If the solution is
;;;;;;; non-null, it breaks out of the loop and returns the solution.
;;;;;;;
;;;;;;; One thing you should note is that DO-POP also builds a little hash
;;;;;;; table called *operators-for-precond*.  I think you will find this
;;;;;;; useful in one of your functions.

(defparameter *depth-increment* 1
  "The depth to increment in iterative deepening search")

;;; This is used to cache the operators by precond.  You might find this
;;; useful to make your ALL-OPERATORS code much much much faster than the
;;; obvious dorky way to do it.
(defparameter *operators-for-precond* nil
  "Hash table.  Will yield a list of operators which can achieve a given precondition")

(defparameter *sorted-list-of-list-of-operators* nil
  "List.  Will yield a list of list of operators sorted by the number of operators in each list")

(defun build-operators-for-precond ()
  "Buils the hash table"
  (setf *operators-for-precond* (make-hash-table :test #'equalp))
  (dolist (operator *operators*)
    (dolist (effect (operator-effects operator))
      (push operator (gethash effect *operators-for-precond*)))))


(defun do-pop ()
  (let* ((start (make-operator
		  :name 'start
		   :uniq (gensym)
		    :preconditions nil
		     :effects *start-effects*))
	  (goal (make-operator
		 :name 'goal
		 :uniq (gensym)
		 :preconditions *goal-preconditions*
		 :effects nil))
	   (plan (make-plan
		  :operators (list start goal)
		  :orderings (list (cons start goal))
		  :links nil
		  :start start
		  :goal goal))
	    (depth *depth-increment*)
	     solution)
    (build-operators-for-precond)
    ;; Do iterative deepening search on this sucker
    (loop
     (format t "~%Search Depth: ~d" depth)
     (setf solution (select-subgoal plan 0 depth))
     (when solution (return)) ;; break from loop, we're done!
     (incf depth *depth-increment*))
    ;; found the answer if we got here
    (format t "~%Solution Discovered:~%~%")
    solution))





;;;;; TWO-BLOCK-WORLD
;;;;; You have two blocks on the table, A and B.   Pretty simple, no?
(defparameter *operators*
  (list
   ;; move from table operators
   (make-operator :name 'a-table-to-b
		   :preconditions '((t a-on-table) (t b-clear) (t a-clear))
		    :effects '((nil a-on-table) (nil b-clear) (t a-on-b)))
   (make-operator :name 'b-table-to-a
		   :preconditions '((t b-on-table) (t a-clear) (t b-clear))
		    :effects '((nil b-on-table) (nil a-clear) (t b-on-a)))
   ;; move to table operators
   (make-operator :name 'a-b-to-table
		   :preconditions '((t a-on-b) (t a-clear))
		    :effects '((t a-on-table) (nil a-on-b) (t b-clear)))
   (make-operator :name 'b-a-to-table
		   :preconditions '((t b-on-a) (t b-clear))
		    :effects '((t b-on-table) (nil b-on-a) (t a-clear))))
  "A list of strips operators without their uniq gensyms set yet -- 
doesn't matter really -- but NOT including a goal or start operator")


;;; b is on top of a
(defparameter *start-effects*
  '((t a-on-table) (t b-on-a) (t b-clear)))

;;; a is on top of b
(defparameter *goal-preconditions*
  ;; somewhat redundant, is doable with just ((t a-on-b))
  '((t a-on-b) (t b-on-table) (t a-clear)))


;;;;;; A solution to the two-block blocks world problem:
;;;; CL-USER> (do-pop)
;;;; 
;;;; Search Depth: 1
;;;; Search Depth: 2
;;;; Search Depth: 3
;;;; Search Depth: 4
;;;; Search Depth: 5
;;;; Search Depth: 6
;;;; Search Depth: 7
;;;; Search Depth: 8
;;;; Search Depth: 9
;;;; Solution Discovered:
;;;; 
;;;; #< PLAN operators: 
;;;; #S(OPERATOR
;;;;    :NAME B-A-TO-TABLE
;;;;    :UNIQ G7317
;;;;    :PRECONDITIONS ((T B-ON-A) (T B-CLEAR))
;;;;    :EFFECTS ((T B-ON-TABLE) (NIL B-ON-A) (T A-CLEAR)))
;;;; #S(OPERATOR
;;;;    :NAME A-TABLE-TO-B
;;;;    :UNIQ G7315
;;;;    :PRECONDITIONS ((T A-ON-TABLE) (T B-CLEAR) (T A-CLEAR))
;;;;    :EFFECTS ((NIL A-ON-TABLE) (NIL B-CLEAR) (T A-ON-B)))
;;;; #S(OPERATOR
;;;;    :NAME START
;;;;    :UNIQ G7234
;;;;    :PRECONDITIONS NIL
;;;;    :EFFECTS ((T A-ON-TABLE) (T B-ON-A) (T B-CLEAR)))
;;;; #S(OPERATOR
;;;;    :NAME GOAL
;;;;    :UNIQ G7235
;;;;    :PRECONDITIONS ((T A-ON-B) (T B-ON-TABLE) (T A-CLEAR))
;;;;    :EFFECTS NIL) 
;;;; links: 
;;;; #< (G7317)B-A-TO-TABLE -> (G7235)GOAL : (T A-CLEAR) >
;;;; #< (G7317)B-A-TO-TABLE -> (G7235)GOAL : (T B-ON-TABLE) >
;;;; #< (G7234)START -> (G7317)B-A-TO-TABLE : (T B-CLEAR) >
;;;; #< (G7234)START -> (G7317)B-A-TO-TABLE : (T B-ON-A) >
;;;; #< (G7317)B-A-TO-TABLE -> (G7315)A-TABLE-TO-B : (T A-CLEAR) >
;;;; #< (G7234)START -> (G7315)A-TABLE-TO-B : (T B-CLEAR) >
;;;; #< (G7234)START -> (G7315)A-TABLE-TO-B : (T A-ON-TABLE) >
;;;; #< (G7315)A-TABLE-TO-B -> (G7235)GOAL : (T A-ON-B) > 
;;;; orderings: 
;;;; #[ (G7317)B-A-TO-TABLE -> (G7315)A-TABLE-TO-B ]
;;;; #[ (G7317)B-A-TO-TABLE -> (G7235)GOAL ]
;;;; #[ (G7234)START -> (G7317)B-A-TO-TABLE ]
;;;; #[ (G7315)A-TABLE-TO-B -> (G7235)GOAL ]
;;;; #[ (G7234)START -> (G7315)A-TABLE-TO-B ]
;;;; #[ (G7234)START -> (G7235)GOAL ]
;;;; >

;; mine
;; #< PLAN operators: 
;; #S(OPERATOR :NAME B-A-TO-TABLE :UNIQ G67849
;;    :PRECONDITIONS ((T B-ON-A) (T B-CLEAR))
;;    :EFFECTS ((T B-ON-TABLE) (NIL B-ON-A) (T A-CLEAR)))
;; #S(OPERATOR :NAME B-A-TO-TABLE :UNIQ G67848
;;    :PRECONDITIONS ((T B-ON-A) (T B-CLEAR))
;;    :EFFECTS ((T B-ON-TABLE) (NIL B-ON-A) (T A-CLEAR)))
;; #S(OPERATOR :NAME A-TABLE-TO-B :UNIQ G67847
;;    :PRECONDITIONS ((T A-ON-TABLE) (T B-CLEAR) (T A-CLEAR))
;;    :EFFECTS ((NIL A-ON-TABLE) (NIL B-CLEAR) (T A-ON-B)))
;; #S(OPERATOR :NAME START :UNIQ G63352 :PRECONDITIONS NIL
;;    :EFFECTS ((T A-ON-TABLE) (T B-ON-A) (T B-CLEAR)))
;; #S(OPERATOR :NAME GOAL :UNIQ G63353
;;    :PRECONDITIONS ((T A-ON-B) (T B-ON-TABLE) (T A-CLEAR)) :EFFECTS NIL) 
;; links: 
;; #< (G67849)B-A-TO-TABLE -> (G63353)GOAL : (T A-CLEAR) >
;; #< (G67848)B-A-TO-TABLE -> (G63353)GOAL : (T B-ON-TABLE) >
;; #< (G67847)A-TABLE-TO-B -> (G63353)GOAL : (T A-ON-B) > 
;; orderings: 
;; #[ (G67849)B-A-TO-TABLE -> (G63353)GOAL ]
;; #[ (G67849)B-A-TO-TABLE -> (G63353)GOAL ]
;; #[ (G63352)START -> (G67849)B-A-TO-TABLE ]
;; #[ (G67848)B-A-TO-TABLE -> (G63353)GOAL ]
;; #[ (G67848)B-A-TO-TABLE -> (G63353)GOAL ]
;; #[ (G63352)START -> (G67848)B-A-TO-TABLE ]
;; #[ (G67847)A-TABLE-TO-B -> (G63353)GOAL ]
;; #[ (G67847)A-TABLE-TO-B -> (G63353)GOAL ]
;; #[ (G63352)START -> (G67847)A-TABLE-TO-B ]
;; #[ (G63352)START -> (G63353)GOAL ]



;;;;;; THREE-BLOCK-WORLD
;;;;;; you have three blocks on the table, A, B, and C.
;;;;;;
;;;;;;
;;;
;;; Why so many operators?  Because we don't have a variable facility.
;;; We can't say MOVE(x,y,z) -- we can only say MOVE(A,TABLE,B).  To
;;; add in a variable facility is a lot more coding, and I figured I'd
;;; save you the hassle of unification.  If you want to give it a shot,
;;; I have written up some unification code which might help you out.
;;; Another consequence of not having a variable facility is that you
;;; can't rely on the least-commitment heuristic of not immediately
;;; binding variables to constants.  For us, we must *immediately*
;;; commit to constants.  That makes our search space much nastier.
;;; C'est la vie!
;;;
;; (defparameter *operators*
;;   (list
;;    ;; move from table operators
;;    (make-operator :name 'a-table-to-b
;;   :preconditions '((t a-on-table) (t b-clear) (t a-clear))
;;   :effects '((nil a-on-table) (nil b-clear) (t a-on-b)))
;;    (make-operator :name 'a-table-to-c
;;   :preconditions '((t a-on-table) (t c-clear) (t a-clear))
;;   :effects '((nil a-on-table) (nil c-clear) (t a-on-c)))
;;    (make-operator :name 'b-table-to-a
;;   :preconditions '((t b-on-table) (t a-clear) (t b-clear))
;;   :effects '((nil b-on-table) (nil a-clear) (t b-on-a)))
;;    (make-operator :name 'b-table-to-c
;;   :preconditions '((t b-on-table) (t c-clear) (t b-clear))
;;   :effects '((nil b-on-table) (nil c-clear) (t b-on-c)))
;;    (make-operator :name 'c-table-to-a
;;   :preconditions '((t c-on-table) (t a-clear) (t c-clear))
;;   :effects '((nil c-on-table) (nil a-clear) (t c-on-a)))
;;    (make-operator :name 'c-table-to-b
;;   :preconditions '((t c-on-table) (t b-clear) (t c-clear))
;;   :effects '((nil c-on-table) (nil b-clear) (t c-on-b)))
;;    ;; move to table operators
;;    (make-operator :name 'a-b-to-table
;;   :preconditions '((t a-on-b) (t a-clear))
;;   :effects '((t a-on-table) (nil a-on-b) (t b-clear)))
;;    (make-operator :name 'a-c-to-table
;;   :preconditions '((t a-on-c) (t a-clear))
;;   :effects '((t a-on-table) (nil a-on-c) (t c-clear)))
;;    (make-operator :name 'b-a-to-table
;;   :preconditions '((t b-on-a) (t b-clear))
;;   :effects '((t b-on-table) (nil b-on-a) (t a-clear)))
;;    (make-operator :name 'b-c-to-table
;;   :preconditions '((t b-on-c) (t b-clear))
;;   :effects '((t b-on-table) (nil b-on-c) (t c-clear)))
;;    (make-operator :name 'c-a-to-table
;;   :preconditions '((t c-on-a) (t c-clear))
;;   :effects '((t c-on-table) (nil c-on-a) (t a-clear)))
;;    (make-operator :name 'c-b-to-table
;;   :preconditions '((t c-on-b) (t c-clear))
;;   :effects '((t c-on-table) (nil c-on-b) (t b-clear)))
;;    ;; block-to-block operators
;;    (make-operator :name 'a-b-to-c
;;   :preconditions '((t a-on-b) (t a-clear) (t c-clear))
;;   :effects '((nil a-on-b) (t a-on-c) (nil c-clear) (t b-clear)))
;;    (make-operator :name 'a-c-to-b
;;   :preconditions '((t a-on-c) (t a-clear) (t b-clear))
;;   :effects '((nil a-on-c) (t a-on-b) (nil b-clear) (t c-clear)))
;;    (make-operator :name 'b-a-to-c
;;   :preconditions '((t b-on-a) (t b-clear) (t c-clear))
;;   :effects '((nil b-on-a) (t b-on-c) (nil c-clear) (t a-clear)))
;;    (make-operator :name 'b-c-to-a
;;   :preconditions '((t b-on-c) (t b-clear) (t a-clear))
;;   :effects '((nil b-on-c) (t b-on-a) (nil a-clear) (t c-clear)))
;;    (make-operator :name 'c-a-to-b
;;   :preconditions '((t c-on-a) (t c-clear) (t b-clear))
;;   :effects '((nil c-on-a) (t c-on-b) (nil b-clear) (t a-clear)))
;;    (make-operator :name 'c-b-to-a
;;   :preconditions '((t c-on-b) (t c-clear) (t a-clear))
;;   :effects '((nil c-on-b) (t c-on-a) (nil a-clear) (t b-clear))))
;;   "A list of strips operators without their uniq gensyms set yet -- 
;; doesn't matter really -- but NOT including a goal or start operator")

;; (defparameter *start-effects*
;;   ;; Sussman Anomaly
;;   '((t a-on-table) (t b-on-table) (t c-on-a) (t b-clear) (t c-clear))
;;   "A list of predicates which specify the initial state")

;; (defparameter *start-effects*
;;   ;; another simple situation: all on table
;;   '((t a-on-table) (t a-clear)
;;     (t b-on-table) (t b-clear)
;;     (t c-on-table) (t c-clear))) 

;; (defparameter *goal-preconditions*
;;   '((t a-on-b) (t b-on-c) (t c-on-table) (t a-clear)))


;;;; An Example on the Sussman Anomaly:


;;;; CL-USER> (do-pop)
;;;;
;;;; Search Depth: 1
;;;; Search Depth: 2
;;;; Search Depth: 3
;;;; Search Depth: 4
;;;; Search Depth: 5
;;;; Search Depth: 6
;;;; Search Depth: 7
;;;; Search Depth: 8
;;;; Search Depth: 9
;;;; Search Depth: 10
;;;; Search Depth: 11
;;;; Search Depth: 12
;;;; Search Depth: 13
;;;; Solution Discovered:
;;;;
;;;; #< PLAN operators: 
;;;; #S(OPERATOR
;;;;    :NAME C-A-TO-TABLE
;;;;    :UNIQ G7120
;;;;    :PRECONDITIONS ((T C-ON-A) (T C-CLEAR))
;;;;    :EFFECTS ((T C-ON-TABLE) (NIL C-ON-A) (T A-CLEAR)))
;;;; #S(OPERATOR
;;;;    :NAME A-TABLE-TO-B
;;;;    :UNIQ G7110
;;;;    :PRECONDITIONS ((T A-ON-TABLE) (T B-CLEAR) (T A-CLEAR))
;;;;    :EFFECTS ((NIL A-ON-TABLE) (NIL B-CLEAR) (T A-ON-B)))
;;;; #S(OPERATOR
;;;;    :NAME B-TABLE-TO-C
;;;;    :UNIQ G7102
;;;;    :PRECONDITIONS ((T B-ON-TABLE) (T C-CLEAR) (T B-CLEAR))
;;;;    :EFFECTS ((NIL B-ON-TABLE) (NIL C-CLEAR) (T B-ON-C)))
;;;; #S(OPERATOR
;;;;    :NAME START
;;;;    :UNIQ G6393
;;;;    :PRECONDITIONS NIL
;;;;    :EFFECTS ((T A-ON-TABLE) (T B-ON-TABLE) (T C-ON-A) (T B-CLEAR) (T C-CLEAR)))
;;;; #S(OPERATOR
;;;;    :NAME GOAL
;;;;    :UNIQ G6394
;;;;    :PRECONDITIONS ((T B-ON-C) (T A-ON-B) (T A-CLEAR) (T C-ON-TABLE))
;;;;    :EFFECTS NIL) 
;;;; links: 
;;;; #< (G7120)C-A-TO-TABLE -> (G6394)GOAL : (T C-ON-TABLE) >
;;;; #< (G7120)C-A-TO-TABLE -> (G6394)GOAL : (T A-CLEAR) >
;;;; #< (G6393)START -> (G7120)C-A-TO-TABLE : (T C-CLEAR) >
;;;; #< (G6393)START -> (G7120)C-A-TO-TABLE : (T C-ON-A) >
;;;; #< (G7120)C-A-TO-TABLE -> (G7110)A-TABLE-TO-B : (T A-CLEAR) >
;;;; #< (G6393)START -> (G7110)A-TABLE-TO-B : (T B-CLEAR) >
;;;; #< (G6393)START -> (G7110)A-TABLE-TO-B : (T A-ON-TABLE) >
;;;; #< (G7110)A-TABLE-TO-B -> (G6394)GOAL : (T A-ON-B) >
;;;; #< (G6393)START -> (G7102)B-TABLE-TO-C : (T B-CLEAR) >
;;;; #< (G6393)START -> (G7102)B-TABLE-TO-C : (T C-CLEAR) >
;;;; #< (G6393)START -> (G7102)B-TABLE-TO-C : (T B-ON-TABLE) >
;;;; #< (G7102)B-TABLE-TO-C -> (G6394)GOAL : (T B-ON-C) > 
;;;; orderings: 
;;;; #[ (G7120)C-A-TO-TABLE -> (G7110)A-TABLE-TO-B ]
;;;; #[ (G7120)C-A-TO-TABLE -> (G6394)GOAL ]
;;;; #[ (G6393)START -> (G7120)C-A-TO-TABLE ]
;;;; #[ (G7102)B-TABLE-TO-C -> (G7110)A-TABLE-TO-B ]
;;;; #[ (G7110)A-TABLE-TO-B -> (G6394)GOAL ]
;;;; #[ (G6393)START -> (G7110)A-TABLE-TO-B ]
;;;; #[ (G7102)B-TABLE-TO-C -> (G6394)GOAL ]
;;;; #[ (G6393)START -> (G7102)B-TABLE-TO-C ]
;;;; #[ (G6393)START -> (G6394)GOAL ]
;;;; >


;;;; You should have almost no warnings from compilation.  Here are the warnings I
;;;; get on openmcl:
;; ? ;;;Compile /Users/sean/Classes/cs687/SimplePlan.lisp
;; ;Compiler warnings for "/Users/sean/Classes/cs687/SimplePlan.lisp" :
;; ;   Undeclared free variable *OPERATORS-FOR-PRECOND*, in ALL-OPERATORS.
;; ;   Undeclared free variable *OPERATORS*, in BUILD-OPERATORS-FOR-PRECOND.
;; ;   Undeclared free variable *START-EFFECTS*, in DO-POP.
;; ;   Undeclared free variable *GOAL-PRECONDITIONS*, in DO-POP.
;; #P"/Users/sean/Classes/cs687/SimplePlan.dfsl"
;; T
;; T

;;;; These are the four global variables that haven't been set yet prior
;;;; to running the plan, so that's expected that they're undeclared.

;;;; Similarly, here are the warnings on CLISP:
;; [2]> ;;;Compile /Users/sean/Classes/cs687/SimplePlan.lisp
;; Compiling file /Users/sean/Classes/cs687/SimplePlan.lisp ...
;; WARNING in function #:TOP-LEVEL-FORM-6 in lines 47..54 :
;; Function COPY-PLAN
;;  was already defined in lines 32..35
;; WARNING in function #:TOP-LEVEL-FORM-7 in lines 56..62 :
;; Function COPY-OPERATOR
;;  was already defined in lines 1..16
;; WARNING in function ALL-OPERATORS in lines 132..135 :
;; *OPERATORS-FOR-PRECOND* is neither declared nor bound,
;; it will be treated as if it were declared SPECIAL.
;; WARNING in function BUILD-OPERATORS-FOR-PRECOND in lines 301..306 :
;; *OPERATORS* is neither declared nor bound,
;; it will be treated as if it were declared SPECIAL.
;; WARNING in function DO-POP in lines 313..341 :
;; *START-EFFECTS* is neither declared nor bound,
;; it will be treated as if it were declared SPECIAL.
;; WARNING in function DO-POP in lines 313..341 :
;; *GOAL-PRECONDITIONS* is neither declared nor bound,
;; it will be treated as if it were declared SPECIAL.

;; Compilation of file /Users/sean/Classes/cs687/SimplePlan.lisp is finished.
;; The following special variables were defined too late:
;;  *OPERATORS-FOR-PRECOND* *OPERATORS* *START-EFFECTS*
;;  *GOAL-PRECONDITIONS*
;; 0 errors, 6 warnings
;; #P"/Users/sean/Classes/cs687/SimplePlan.fas" ;
;; 6 ;
;; 6

;;;; Here it's also complaining about copy-operator and copy-plan being
;;;; redefined, because the structure definition had created them and
;;;; I'm doing better copy functions.  That's expected.


;;Our solutions:

;;2 block world

;; Solution Discovered:

;; #< PLAN operators: 
;; #S(OPERATOR :NAME B-A-TO-TABLE :UNIQ G20485 :PRECONDITIONS ((T B-ON-A) (T B-CLEAR))
;;    :EFFECTS ((T B-ON-TABLE) (NIL B-ON-A) (T A-CLEAR)))
;; #S(OPERATOR :NAME A-TABLE-TO-B :UNIQ G20484
;;    :PRECONDITIONS ((T A-ON-TABLE) (T B-CLEAR) (T A-CLEAR))
;;    :EFFECTS ((NIL A-ON-TABLE) (NIL B-CLEAR) (T A-ON-B)))
;; #S(OPERATOR :NAME START :UNIQ G20431 :PRECONDITIONS NIL
;;    :EFFECTS ((T A-ON-TABLE) (T B-ON-A) (T B-CLEAR)))
;; #S(OPERATOR :NAME GOAL :UNIQ G20432 :PRECONDITIONS ((T A-ON-B) (T B-ON-TABLE) (T A-CLEAR))
;;    :EFFECTS NIL) 
;; links: 
;; #< (G20485)B-A-TO-TABLE -> (G20432)GOAL : (T A-CLEAR) >
;; #< (G20485)B-A-TO-TABLE -> (G20432)GOAL : (T B-ON-TABLE) >
;; #< (G20431)START -> (G20485)B-A-TO-TABLE : (T B-CLEAR) >
;; #< (G20431)START -> (G20485)B-A-TO-TABLE : (T B-ON-A) >
;; #< (G20485)B-A-TO-TABLE -> (G20484)A-TABLE-TO-B : (T A-CLEAR) >
;; #< (G20431)START -> (G20484)A-TABLE-TO-B : (T B-CLEAR) >
;; #< (G20431)START -> (G20484)A-TABLE-TO-B : (T A-ON-TABLE) >
;; #< (G20484)A-TABLE-TO-B -> (G20432)GOAL : (T A-ON-B) > 
;; orderings: 
;; #[ (G20485)B-A-TO-TABLE -> (G20484)A-TABLE-TO-B ]
;; #[ (G20431)START -> (G20484)A-TABLE-TO-B ]
;; #[ (G20485)B-A-TO-TABLE -> (G20484)A-TABLE-TO-B ]
;; #[ (G20485)B-A-TO-TABLE -> (G20432)GOAL ]
;; #[ (G20431)START -> (G20485)B-A-TO-TABLE ]
;; #[ (G20484)A-TABLE-TO-B -> (G20432)GOAL ]
;; #[ (G20431)START -> (G20484)A-TABLE-TO-B ]
;; #[ (G20431)START -> (G20432)GOAL ]



;;3 block world
;; Solution Discovered:

;; #< PLAN operators: 
;; #S(OPERATOR :NAME B-TABLE-TO-C :UNIQ G20286
;;    :PRECONDITIONS ((T B-ON-TABLE) (T C-CLEAR) (T B-CLEAR))
;;    :EFFECTS ((NIL B-ON-TABLE) (NIL C-CLEAR) (T B-ON-C)))
;; #S(OPERATOR :NAME A-TABLE-TO-B :UNIQ G20268
;;    :PRECONDITIONS ((T A-ON-TABLE) (T B-CLEAR) (T A-CLEAR))
;;    :EFFECTS ((NIL A-ON-TABLE) (NIL B-CLEAR) (T A-ON-B)))
;; #S(OPERATOR :NAME START :UNIQ G19545 :PRECONDITIONS NIL
;;    :EFFECTS
;;    ((T A-ON-TABLE) (T A-CLEAR) (T B-ON-TABLE) (T B-CLEAR) (T C-ON-TABLE) (T C-CLEAR)))
;; #S(OPERATOR :NAME GOAL :UNIQ G19546
;;    :PRECONDITIONS ((T A-ON-B) (T B-ON-C) (T C-ON-TABLE) (T A-CLEAR)) :EFFECTS NIL) 
;; links: 
;; #< (G19545)START -> (G19546)GOAL : (T A-CLEAR) >
;; #< (G19545)START -> (G19546)GOAL : (T C-ON-TABLE) >
;; #< (G19545)START -> (G20286)B-TABLE-TO-C : (T B-CLEAR) >
;; #< (G19545)START -> (G20286)B-TABLE-TO-C : (T C-CLEAR) >
;; #< (G19545)START -> (G20286)B-TABLE-TO-C : (T B-ON-TABLE) >
;; #< (G20286)B-TABLE-TO-C -> (G19546)GOAL : (T B-ON-C) >
;; #< (G19545)START -> (G20268)A-TABLE-TO-B : (T A-CLEAR) >
;; #< (G19545)START -> (G20268)A-TABLE-TO-B : (T B-CLEAR) >
;; #< (G19545)START -> (G20268)A-TABLE-TO-B : (T A-ON-TABLE) >
;; #< (G20268)A-TABLE-TO-B -> (G19546)GOAL : (T A-ON-B) > 
;; orderings: 
;; #[ (G20286)B-TABLE-TO-C -> (G20268)A-TABLE-TO-B ]
;; #[ (G19545)START -> (G20268)A-TABLE-TO-B ]
;; #[ (G20286)B-TABLE-TO-C -> (G19546)GOAL ]
;; #[ (G19545)START -> (G20286)B-TABLE-TO-C ]
;; #[ (G20268)A-TABLE-TO-B -> (G19546)GOAL ]
;; #[ (G19545)START -> (G20268)A-TABLE-TO-B ]
;; #[ (G19545)START -> (G19546)GOAL ]