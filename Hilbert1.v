Load "Tactics4_Constructions.v".

Section INCIDENCE.

(* On verifie que les axiomes d'incidence du systeme de Hilbert sont des theoremes dans notre systeme d'axiomes. *)

(* I1 : For any two points A, B, there exists a line L containing A, B. If A and B are distincts points, L is a unique line.*)

Lemma I1 : forall A B : Point, exists d : Line, OnLine d A /\ OnLine d B.
Proof.
	intros; byApartCases Oo Uu ipattern:A.
	 by3Cases Oo A B.
	  setLine A B ipattern:d.
	    answerIs d.
	  setLine A B ipattern:d.
	    answerIs d.
	  setLine Oo A ipattern:d.
	    answerIs d.
	 by3Cases Uu A B.
	  setLine A B ipattern:d.
	    answerIs d.
	  setLine A B ipattern:d.
	    answerIs d.
	  setLine Uu A ipattern:d.
	    answerIs d.
Qed.

Lemma I1' : forall A B : Point, forall d1 d2 : Line, 
	A <> B -> OnLine d1 A -> OnLine d1 B -> OnLine d2 A -> OnLine d2 B ->
	EqLine d1 d2.
Proof.
	intros.
	step H.
Qed.

(* I2 : Every line contains at least two points. *)

Lemma I2 : forall d : Line, exists A : Point, exists B : Point, A <> B /\ OnLine d A /\ OnLine d B.
Proof.
	intros; destruct d.
	answerIs A; answerIs B.
Qed.

(* I3 : There exist three noncollinear points (that is, three points not all contained in a single line). *)

Lemma I3 : exists A : Point, exists B : Point, exists C : Point, forall d : Line, 
	~(OnLine d A /\ OnLine d B /\ OnLine d C).
Proof.
	answerIs Oo; answerIs Uu; answerIs Vv; intros.
	since (~ Collinear Oo Uu Vv).
	contrapose H.
	step d; canonize.
Qed.

End INCIDENCE.

