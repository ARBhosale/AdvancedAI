;;Contributors :  Aniket Bhosale and Brinston Gonsalves




;;;; We tried to extend the extend the assignment to 3 heap nim by converting the 2d array to 3d array and then creating the required support functions but got stuck with it while fetching the maximum q value from the 3d array and thus decided  to submit the existing working file.






;Reinforcement Learning Project
;
;This should not be particularly difficult, and you could probably get it done this week if you wished.
;A Q-learner that learns to play Nim.
;
;This project is an easy assignment.
;What I'm asking you to do is to complete the assignment, then
;"enhance" it in some way.  Try three heaps; try prioritorized sweeping
;(ask me); try comparing approaches to alpha, gamma, action-selection procedures,
;ways of implementing the "opponent, etc.  Try extending to 3-Heap Nim.
;Something fun.
;
;You might also try to analyze what happens when you try random opponents versus co-adaptive ones.  Advantages?  Disadvantages?
;
;ABOUT NIM
;---------
;There are several versions of Nim.  The version we will play is called 1-Heap Nim
;and it goes like this:
;
;1. Put N sticks in a pile (called a "heap")
;2. Players take turns taking 1, 2, or 3 sticks out of the heap.
;3. Whoever has to take out the last stick loses.
;
;
;LEARNING NIM
;------------
;
;Our Q-learner will build a Q-table solely through playing itself over and over
;again.  The table will tell it, ultimately, how smart it is to do a given move
;(take 1, 2, or 3 sticks) in a given state (number of sticks taken out so far).
;Q values will all start at 0.
;
;We will define the actions as follows:
;
;Action 0: take 1 stick out
;Action 1: take 2 sticks out
;Action 2: take 3 sticks out
;
;Thus the action number is exactly 1- the number of sticks to take out.  Keep
;this in mind -- the Q table will store Q values by action number, NOT by
;sticks taken out.
;
;We will define the states as follows:
;
;State 0: no sticks removed from heap
;State 1: 1 stick removed from heap
;...
;State N: N sticks removed from heap
;
;You will probably find it useful for the number of states in the Q table to
;be, believe it or not, about 6 larger than the heap size.  Thus there are
;some states at the high end of the table which represent, more or less,
;"negative heap sizes".  Of course, you can never play a negative heap size;
;such q-values will stay 0.
;
;Our Q table will be a STATE x ACTION array.  I have given you some functions
;which should make it easy to use this array:  NUM-STATES, NUM-ACTIONS,
;MAKE-Q-TABLE, MAX-Q, and MAX-ACTION.
;
;The Q learner will learn by playing itself: the learner records the current
;state, makes a move, lets the ``opponent'' make a move, then notes the new
;resulting state.  The action is the move the learner made.  Now we have s,
;a, and s'.  Note that s' is the state AFTER the opponent made his move.
;
;After the Q learner has learned the game, then you can play the learner
;and see how well it does.
;
;
;WHAT YOU NEED TO DO
;-------------------
;
;Your job is to implement several functions:
;
;Q-LEARNER
;  (the Q update function)
;LEARN-NIM
;  (the learning algorithm, tweaked for Nim -- the longest function)
;PLAY-NIM
;  (lets you play against the learned Q table)
;BEST-ACTIONS
;  (prints out the best actions believed so far)
;
;To help you, I've written a basic ALPHA function, and MAKE-USER-MOVE
;and ASK-IF-USER-GOES-FIRST functions.  I predict you will find them helpful.
;
;
;
;THE SECRET OF NIM (ugh, that was bad)
;-----------------
;
;You can get an idea for how well these settings perform by seeing what's
;usually the smallest number of iterations necessary before BEST-ACTIONS starts
;reporting the correct actions.
;
;So what ARE the correct actions in Nim?  There is a very simple rule for playing
;Nim.  If there are N sticks left in the pile, you want to remove sticks so that
;N = 1 + 4A where A is some number.  Then whatever your opponent takes out, you take
;4 minus that number, so your sticks and your opponent's sticks removed sum to 4.
;Keep on doing this, and eventually the A's will get dropped and your opponent will
;be left with 1 stick, which he must take.
;
;Depending on the size of the Nim heap, the game is either a guaranteed win for
;the first player or for the second player.  It all depends on who can get it down
;to 1 + 4A first.
;
;You will discover a certain pattern emerge in your BEST-ACTIONS list.  The first
;couple of values may be odd, but then from there on out you'll see
;2, 1, 0, <any>, 2, 1, 0, <any>, etc.  This is because in each of those heap
;values, the right move is to remove 3, 2, or 1 sticks, or (in the <any> value)
;it doesn't matter because you're guaranteed to lose at that heap size.  In essence
;you want to get your OPPONENT down to the <any> value (it's the 1 + 4A number).
;
;
;VERY STRONG HINT
;
;Keep in mind how the Q table is structured: actions are stored in the slot
;1 less than the number of sticks removed by that action.  And states go UP
;as more sticks are removed.   You may need to do some 1-'s and 1+'s to play
;the right action.
;
;
;INTERESTING TRIVIA
;
;Nim's been done a lot.  I was going to do tic-tac-toe, but decided it was too
;evil.  :-)



(defun random-elt (sequence)
  "Returns a random element from a sequence"
  (elt sequence (random (length sequence))))

(defun num-states (q-table)
  "Returns the number of states in a q-table"
  (first (array-dimensions q-table)))

(defun num-actions (q-table &optional state)
  "Returns the number of actions in a q-table"
  (second (array-dimensions q-table)))

(defun make-q-table (num-states num-actions)
  "Makes a q-table, with initial values all set to 0"
  (make-array (list num-states num-actions) :initial-element 0))

(defun max-q (q-table state)
  "Returns the highest q-value for a given state over all possible actions.
If the state is outside the range, then utility-for-outside-state-range is returned."
  (let* ((num-actions (num-actions q-table))
	 (best (aref q-table state (1- num-actions))))  ;; q of last action
    (dotimes (action (1- num-actions) best)  ;; all but last action...
      (setf best (max (aref q-table state action) best)))))

(defun max-action (q-table state &optional val)
  "Returns the action which provided the highest q-value.  If val is not provided, ties are broken at random;
else val is returned instead when there's a tie. If state is outside the range, then an error is generated
 (probably array-out-of-bounds)."
  ;; a little inefficient, but what the heck...
  (let ((num-actions (num-actions q-table))
	(best (max-q q-table state))
	bag)
    (dotimes (action num-actions)
      (when (= (aref q-table state action) best)
	(push action bag)))
    (if (and val (rest bag))
	val
      (random-elt bag))))

(defparameter *basic-alpha* 0.5 "A simple alpha constant")
(defun basic-alpha (iteration)
  (declare (ignore iteration)) ;; quiets compiler complaints
  *basic-alpha*)

(defun get-probability (new-state-index old-state-index action-index)
  (if (= new-state-index (+ old-state-index (+ action-index 1)))
    0.8 0.2))

(defun get-reward (current-state-index heap-size)
  (cond ((= (1+ current-state-index) (1- heap-size)) -1)
    ((= (1+ current-state-index) heap-size) 1)
    (t 0)))

(defun get-future-utility (current-state-index action-index q-table)
;; using Algorithm number 123
  (let* ((future-utility 0))
    (setf state-index current-state-index)
    (dotimes (state-index (num-states q-table))
      (setf future-utility (+ future-utility
        (* (get-probability state-index current-state-index action-index)
          (max-q q-table state-index)))))))

(defun q-learner (q-table reward current-state action next-state gamma alpha-func iteration)
  "Modifies the q-table and returns it.  alpha-func is a function which must be called
to provide the current alpha value."

  ;;; IMPLEMENT ME


  (let (
	 (alpha (funcall alpha-func iteration))
        )

    

;    (print q-table)
    
     
	  
    (setf (aref q-table current-state action)
	  (+ (* (- 1 alpha) (aref q-table current-state action))
	     (* alpha (+ reward (* gamma (max-q q-table next-state))))
	  )
    )
    
    
    q-table
  )
 

)

(defun ask-if-user-goes-first ()
  "Returns true if the user wants to go first"
  (y-or-n-p "Do you want to play first?"))

(defun make-user-move ()
  "Returns the number of sticks the user wants to remove"
  (let ((result))
    (loop
     (format t "~%Take how many sticks?  ")
     (setf result (read))
     (when (and (numberp result) (<= result 3) (>= result 1))
       (return result))
     (format t "~%Answer must be between 1 and 3"))))

(defun play-nim (q-table heap-size)
  "Plays a game of nim.  Asks if the user wants to play first,
then has the user play back and forth with the game until one of
them wins.  Reports the winner."

  ;;; IMPLEMENT ME

  (let (player
	(state 0)
	) 

    (if (ask-if-user-goes-first)
	(setf player 0) ;user
	(setf player 1) ;computer
    )
    
    (loop

       (format t "Current State : ~S~%"state)

       
       (if (eq player 0)
	   (let ((user-action (make-user-move)))

	     (setf state (+ state (+ 0 user-action)))
	     
	     (setf player 1)
	     )
	   (let ((computer-action (max-action q-table state)))

	     (format t "Computer Played ~S~%"(+ 1 computer-action))
	     (setf state (+ state (+ 1 computer-action)))	     
	     
	     (setf player 0)
	     )
       )
       

       (when (>= state heap-size)
	 (if (eq player 1)
	     (print "You Lose")
	     (print "You Win")
	 )
	 (return)
       )
    )


  )
)


(defun best-actions (q-table)
  "Returns a list of the best actions.  If there is no best action, this is indicated with a hyphen (-)"
  ;; hint: see optional value in max-action function

  ;;; IMPLEMENT ME

  (let ((output-list '())
	max-act
	)

    (dotimes (i (num-states q-table))

      (setf max-act (max-action q-table i -1))

      (if (<= max-act 0)
	  (setf output-list (append output-list (list '-)))
	  (setf output-list (append output-list (list max-act)))
	  
      )
	     
	     
     )
    

    output-list
   )
  
   
  )



;; Top-level nim learning algorithm.  The function works roughly like this...
;;
;; Make a q table.  Hint: make it 6 states larger than needed.  Can you see why?
;; Iterations times:
;;   Set state to 0  (no sticks removed from heap yet)
;;   Loop:
;;       old state <- state
;;       Determine and make my move, update state
;;       If I lost, set my reward to -1
;;       Determine and make my opponent's move, update state
;;       If the opponent lost, set my reward to +1
;;       If no reward has been set yet, set it to 0
;;       Update q table with the reward, old-state, my move, and current ("next") state
;;       If new state is bigger than the heap size, exit loop
;; Return q table


(defun learn-nim (heap-size gamma alpha-func num-iterations)
  "Returns a q-table after learning how to play nim"
  ;;; IMPLEMENT ME
  
  (let* ((state 0)
	old-state
	(q-table (make-q-table (+ heap-size 6) 3))
	my-move
	reward
	opponents-move 
	
	 )

    (loop for iteration from 1 to num-iterations do

	 (setf state 0)

	 (loop while (< state heap-size) do
;	      (print state)
	      (setf old-state state)
	      (setf my-move (max-action q-table state))

	      (setf state (+ state (+ 1 my-move)))
	      
	      (if (>= state heap-size)
		  (setf reward -1)
		  (progn
		    (setf opponents-move (max-action q-table state)) 
		    (setf state (+ state (+ opponents-move 1)))

		    (if (>= state heap-size)
			(setf reward 1)
			)

		    
		  )
		  )

	      
	      (if (and (not (eq reward 1)) (not (eq reward -1)))
		  (setf reward 0)
		  )
	      
	      (setf q-table (q-learner q-table reward old-state my-move state gamma alpha-func iteration))

;	      (format t "Iteration number : ~S"iteration)
;	      (print q-table)
	      

	 
	 )

     )

    q-table
    
  )
  
  
  
)

;(learn-nim 22 0.1 #'basic-alpha 50000)
;(print (learn-nim 22 0.1 #'basic-alpha 50000))
;; sbcl
;; example:
;; 
(setq *my-q-table* (learn-nim 22 0.1 #'basic-alpha 50000))

;(print *my-q-table*)
;;
;; to get the policy from this table:
;;
; (print (best-actions *my-q-table*))
;;
;; to play a game of your brain versus this q-table:
;;
 (play-nim *my-q-table* 22)   ;; need to provide the original heap size
;;
;; You might try changing to some other function than #'basic-alpha...
