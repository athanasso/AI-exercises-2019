;____________________________________________________
;
; ES solving the simplified version of Packman's Problem
; Author: AI lab
;____________________________________________________

;____________________________________________________

; The problem's World
;____________________________________________________


(deffacts static_facts ;playing field
	(cell_at 1 1 fruits 0)
	(cell_at 1 2 fruits 1)
	(cell_at 1 3 fruits 0)
	(cell_at 1 4 fruits 3)
)

(deffacts moving_facts ;initializing the position of the pacman
	(pacman_at 1 2)
)

;____________________________________________________

;          RULES' SECTION
;add priorities to rules and try different strategies
;____________________________________________________

(defrule begin
	(declare (salience 20)) ;needs to be ran first so it has the highest importance
	(initial-fact)
=>
	(set-strategy random)
)

(defrule reach_goal	;final goal for pacmen
	(declare (salience 10))
	(cell_at 1 1 fruits 0)
	(cell_at 1 2 fruits 0)
	(cell_at 1 3 fruits 0)
	(cell_at 1 4 fruits 0)
=>
	(printout t "All the fruits have been eaten, pacman won!"  crlf) ;print out a message
	(halt) ;exit
)

(defrule move_left ;pacman moves left
	(declare (salience 1))
	?z <- (pacman_at ?x ?y) ;retrieve pacman position
	(cell_at ?x =(- ?y 1) fruits ?f) ;retrieve pacman position cell
=>
	(retract ?z) ;remove old pacman stats
	(assert (pacman_at ?x (- ?y 1))) ;new pacman position
)

(defrule move_right ;pacman moves right
	(declare (salience 1))
	?z <- (pacman_at ?x ?y) ;retrieve pacman position
	(cell_at ?x =(+ ?y 1) fruits ?f) ;retrieve pacman position cell
=>
	(retract ?z) ;remove old pacman stats
	(assert (pacman_at ?x (+ ?y 1))) ;new pacman position
)

(defrule eat_fruit
	(declare (salience 5)) ;needs to be executed first so we know if pacman won
	(pacman_at ?x ?y) ;retrieve pacman position
	?z <- (cell_at ?x ?y  fruits ?f&~0) ;retrieve pacman position cell if it has fruits
=>
	(retract ?z) ;remove old pacman stats
	(assert (cell_at ?x ?y fruits (- ?f 1))) ;clear fruits
)

