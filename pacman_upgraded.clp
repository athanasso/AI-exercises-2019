;-----------------------------------;
;ΤΥΜΟΤΕΟΥΣ ΛΕΟΝΑΡΝΤ ΣΤΕΦΑΝΙΑΚ 171012;
;ΕΜΜΑΝΟΥΗΛ ΑΘΑΝΑΣΟΠΟΥΛΟΣ 171049     ;
;-----------------------------------;
(defglobal
	?*importance* = 0 ;dynamically change the salience(importance) of ghost's moves so it moves interchangeably with the pacmen
	?*pacman1* = 0 ;check if pacman 1 is eaten
	?*pacman2* = 0 ;check if pacman 2 is eaten
)
 
(deffacts static_facts ;playing field
	(cell_at 1 1 fruits 0)                                                        
	(cell_at 1 2 fruits 1)                                                                
	(cell_at 1 3 fruits 0)                                                                 
	(cell_at 1 4 fruits 2)

	(cell_at 2 1 fruits 1)
	(cell_at 2 2 fruits 0)
	(cell_at 2 3 fruits 2)
	(cell_at 2 4 fruits 0)

	(cell_at 3 1 fruits 0)
	(cell_at 3 2 fruits 0)
	(cell_at 3 3 fruits 1)
	(cell_at 3 4 fruits 0)

	(cell_at 4 1 fruits 0)
	(cell_at 4 2 fruits 0)
	(cell_at 4 3 fruits 0)
	(cell_at 4 4 fruits 0)
)

(deffacts moving_facts ;initializing the position of the clyde ghost and pacmen
	(pacman 1 is_in 4 2)
	(pacman 2 is_in 1 2)
	(pacman turn 1) ;determining which pacman moves
	(clyde 3 3)
)

(defrule begin
	(declare (salience 20)) ;needs to be ran first so it has the highest importance
	(initial-fact)
=>
	(set-strategy random)
	(set-salience-evaluation every-cycle) ;checks continuously if salience is changed while running the application
)

(defrule reach_goal ;final goal for pacmen
	(declare (salience 10))
	(cell_at 1 1 fruits 0)
	(cell_at 1 2 fruits 0)
	(cell_at 1 3 fruits 0)
	(cell_at 1 4 fruits 0)

	(cell_at 2 1 fruits 0)
	(cell_at 2 2 fruits 0)
	(cell_at 2 3 fruits 0)
	(cell_at 2 4 fruits 0)

	(cell_at 3 1 fruits 0)
	(cell_at 3 2 fruits 0)
	(cell_at 3 3 fruits 0)
	(cell_at 3 4 fruits 0)

	(cell_at 4 1 fruits 0)
	(cell_at 4 2 fruits 0)
	(cell_at 4 3 fruits 0)
	(cell_at 4 4 fruits 0)
=>
	(printout t "All the fruits have been eaten, pacman won!"  crlf) ;print out a message
	(halt) ;exit
)

(defrule no_more_pacmen ;if all pacmen are dead
	(declare (salience 19))
	(and 
		(not (exists (pacman 1 is_in ?x ?y))) 
		(not (exists (pacman 2 is_in ?x ?y)))
	)
=>
	(printout t "All the pacmen are dead...ghost won." crlf) ;print out a message
	(halt) ;exit
)
;-----------------------------------;
;pacman moves                       ;
;-----------------------------------;
(defrule move_up ;pacman moves up
	(declare (salience 1))
	?a <- (pacman turn ?b) ;retrieve pacman turn so it can be changed
	?z <- (pacman ?b is_in ?x ?y) ;retrieve pacman position
	(cell_at =(- ?x 1) ?y fruits ?f) ;retrieve pacman position cell
=>
	(retract ?z) ;remove old pacman stats
	(assert (pacman ?b is_in (- ?x 1) ?y)) ;new pacman position
	(bind ?*importance* 2) ;change value of global importance
	;change move priority to next pacman only if both are alive
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (retract ?a)
	)
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (if (eq ?b 1)
				then (assert (pacman turn 2))
				else (assert (pacman turn 1)))
	)
)

(defrule move_down ;pacman moves down
	(declare (salience 1))
	?a <- (pacman turn ?b) ;retrieve pacman turn so it can be changed
	?z <- (pacman ?b is_in ?x ?y) ;retrieve pacman position
	(cell_at =(+ ?x 1) ?y fruits ?f) ;retrieve pacman position cell
=>
	(retract ?z) ;remove old pacman stats
	(assert (pacman ?b is_in (+ ?x 1) ?y)) ;new pacman position
	(bind ?*importance* 2) ;change value of global importance
	;change move priority to next pacman only if both are alive
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (retract ?a)
	)
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (if (eq ?b 1)
				then (assert (pacman turn 2))
				else (assert (pacman turn 1)))
	)
)

(defrule move_left ;pacman moves left
	(declare (salience 1))
	?a <- (pacman turn ?b) ;retrieve pacman turn so it can be changed
	?z <- (pacman ?b is_in ?x ?y) ;retrieve pacman position
	(cell_at ?x =(- ?y 1) fruits ?f) ;retrieve pacman position cell
=>
	(retract ?z) ;remove old pacman stats
	(assert (pacman ?b is_in ?x (- ?y 1))) ;new pacman position
	(bind ?*importance* 2) ;change value of global tmimportancep
	;change move priority to next pacman only if both are alive
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (retract ?a)
	)
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (if (eq ?b 1)
				then (assert (pacman turn 2))
				else (assert (pacman turn 1)))
	)
)

(defrule move_right ;pacman moves right
	(declare (salience 1))
	?a <- (pacman turn ?b) ;retrieve pacman turn so it can be changed
	?z <- (pacman ?b is_in ?x ?y) ;retrieve pacman position
	(cell_at ?x =(+ ?y 1) fruits ?f) ;retrieve pacman position cell
=>
	(retract ?z) ;remove old pacman stats
	(assert (pacman ?b is_in ?x (+ ?y 1))) ;new pacman position
	(bind ?*importance* 2) ;change value of global importance
	;change move priority to next pacman only if both are alive
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (retract ?a)
	)
	(if (and (eq ?*pacman1* 0) (eq ?*pacman2* 0))
		then (if (eq ?b 1)
				then (assert (pacman turn 2))
				else (assert (pacman turn 1)))
	)
)

(defrule eat_fruit
	(declare (salience 4)) ;needs to be executed first so we know if pacman won
	(pacman ?pac is_in ?x ?y) ;retrieve pacman position
	?z <- (cell_at ?x ?y  fruits ?f&~0) ;retrieve pacman position cell if it has fruits
=>
	(retract ?z) ;remove old pacman stats
	(assert (cell_at ?x ?y fruits (- ?f 1))) ;clear fruits
)
;-----------------------------------;
;ghost moves                        ;
;-----------------------------------;
(defrule move_up_ghost ;ghost moves up
	(declare (salience ?*importance*)) ;dynamic salience
	?v <- (clyde ?x ?y) ;retrieve ghost position
	(cell_at =(- ?x 1) ?y fruits ?f) ;retrieve ghost position cell
=>
	(retract ?v) ;remove old ghost stats
	(assert (clyde (- ?x 1) ?y)) ;new ghost position
	(bind ?*importance* 0) ;change value of global importance
)

(defrule move_down_ghost ;ghost moves down
	(declare (salience ?*importance*)) ;dynamic salience
	?v <- (clyde ?x ?y) ;retrieve ghost position
	(cell_at =(+ ?x 1) ?y fruits ?f) ;retrieve ghost position cell
=>
	(retract ?v) ;remove old ghost stats
	(assert (clyde (+ ?x 1) ?y)) ;new ghost position
	(bind ?*importance* 0) ;change value of global importance
)

(defrule move_left_ghost ;ghost moves left
	(declare (salience ?*importance*)) ;dynamic salience
	?v <- (clyde ?x ?y) ;retrieve ghost position
	(cell_at ?x =(- ?y 1) fruits ?f) ;retrieve ghost position cell
=>
	(retract ?v) ;remove old ghost stats
	(assert (clyde ?x (- ?y 1))) ;new ghost position
	(bind ?*importance* 0) ;change value of global importance
)

(defrule move_right_ghost ;ghost moves right
	(declare (salience ?*importance*)) ;dynamic salience
	?v <- (clyde ?x ?y) ;retrieve ghost position
	(cell_at ?x =(+ ?y 1) fruits ?f) ;retrieve ghost position cell
=>
	(retract ?v) ;remove old ghost stats
	(assert (clyde ?x (+ ?y 1))) ;new ghost position
	(bind ?*importance* 0) ;change value of global importance
)

(defrule eat_pacman
	(declare (salience 3))
	(clyde ?x ?y) ;retrieve ghost position
	?v <- (pacman ?i is_in ?x ?y) ;retrieve pacman if in same cell as ghost
	?g <- (pacman turn ?j) ;also retrieve its turn so it can be changed
=>
	(retract ?g) ;remove pacman turn
	;and permanently bind it to the other pacman
	;also set the pacman death state to true (1)
	(if (eq ?i 1)
		then (bind ?*pacman1* 1))
	(if (eq ?i 1)
		then (assert (pacman turn 2)))

	(if (eq ?i 2)
		then (bind ?*pacman2* 1))
	(if (eq ?i 2)
		then (assert (pacman turn 1)))
	(retract ?v) ;kill pacman 
)
;//////////////////////////////////////////////