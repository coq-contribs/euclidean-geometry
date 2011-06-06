Load "Hilbert4.v".

Section PARALLEL.

(* Par un point, il passe une parallele a une droite donnee. *)

Theorem E1 (*existence*) : forall A : Point, forall d : Line,
	exists d' : Line, ParallelLines d d' /\ OnLine d' A.
Proof.
	intros.
	destruct d.
	by3Cases A A0 B.
	 setParallel (Ruler A0 B n) A ipattern:d'.
	  simplLine;  immediate.
	  answerIs d'.
	 setParallel (Ruler A0 B n) A ipattern:d'.
	  simplLine; immediate.
	  answerIs d'.
	 answerIs (Ruler A0 B n).
Qed.

(* Cette parallele est unique. *)

Theorem  E2 (*unicity*) : forall A : Point, forall d  d' d'' : Line,
	ParallelLines d d' -> OnLine d' A ->
	ParallelLines d d'' -> OnLine d'' A ->
	EqLine d' d''.
Proof.
	intros.
	step (A, d).
Qed.

End PARALLEL.
