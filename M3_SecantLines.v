Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import E2_NotEquidirectedIntersection .
Require Import L6_Tactics .
Require Import M1_SuperImposedLines M2_ParallelLines.

Section SECANT_LINES.

Lemma TwoPointsSecantLine : forall d1 d2 : Line, forall A B : Point,
	OnLine d1 A ->
	OnLine d2 A ->
	OnLine d1 B ->
	~OnLine d2 B ->
	SecantLines d1 d2.
Proof.
	intros.
	assert (A <> B).
	 apply (OnLineDistinct A B d2); immediate11.
	 contrapose0 H2.
	   assert (EqLine d1 d2).
	  apply (ParallelEqLine A); immediate11.
	  apply (EqLineOnLine d1); immediate11.
Qed.

Lemma EqSecantSecantLines : forall d1 d2 d3 : Line,
	EqLine d1 d2 ->
	SecantLines d1 d3 ->
	SecantLines d2 d3.
Proof.
	intros.
	contrapose0 H0.
	apply ParallelLinesSym; apply (ParallelEqParallelLine d3 d2 d1).
	 apply ParallelLinesSym; immediate11.
	 apply EqLineSym; immediate11.
Qed.

Lemma EqEqSecantSecantLines : forall d1 d2 d3 d4 : Line,
	EqLine d1 d2 ->
	EqLine d3 d4 ->
	SecantLines d1 d3 ->
	SecantLines d2 d4.
Proof.
	intros.
	contrapose0 H1.
	apply (EqEqParallelLine d2 d4).
	 apply EqLineSym; immediate11.
	 apply EqLineSym; immediate11.
	 immediate11.
Qed.

Lemma EqNotSecantLines : forall d1 d2: Line,
	EqLine d1 d2 ->
	~SecantLines d1 d2.
Proof.
	intros.
	intro H0; elim H0.
	apply EqParallelLine; immediate11.
Qed.

Lemma SecantNotEqLines : forall d1 d2: Line,
	SecantLines d1 d2 ->
	~EqLine d1 d2.
Proof.
	intros.
	contrapose0 H.
	apply EqParallelLine; immediate11.
Qed.


Lemma FourPointsSecantLines : forall d1 d2 : Line, forall A B C D: Point,
	OnLine d1 A -> OnLine d1 B ->
	OnLine d2 C -> OnLine d2 D ->
	Clockwise A B C -> 
	~Clockwise A B D -> 
	SecantLines d1 d2.
Proof.
	intros; intro.
	elim (FourPointsSecantLine A B C D H3 H4).
	setLine0 A B ipattern:(d3).
	 immediate11.
	 assert (EqLine d1 d3).
	  apply EqLineDef; immediate11.
	  setLine0 C D ipattern:(d4).
	   step11 H3.
	   assert (EqLine d2 d4).
	    apply EqLineDef; immediate11.
	    assert (ParallelLines d3 d4).
	     apply (EqEqParallelLine d1 d2); immediate11.
	     exact H10.
Qed.

End SECANT_LINES.

