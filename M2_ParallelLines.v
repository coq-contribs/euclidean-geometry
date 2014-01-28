Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import B7_Tactics .
Require Import D3_SecondDimension D5_Tactics .
Require Import E2_NotEquidirectedIntersection .
Require Import L6_Tactics .
Require Import M1_SuperImposedLines.

Section PARALLEL_LINES.

Lemma ParallelLinesRefl : forall d : Line,
	ParallelLines d d.
Proof.
	intro; simplLine1.
	immediate11.
Qed.

Lemma ParallelLinesSym : forall d1 d2 : Line,
	ParallelLines d1 d2 ->
	ParallelLines d2 d1.
Proof.
	intros; simplLine1.
	immediate11.
Qed.

Lemma EqParallelLine : forall d1 d2 : Line,
	EqLine d1 d2 ->
	ParallelLines d1 d2.
Proof.
	intros; inversion H.
	destruct (TwoPointsOnLineOrientation (LineA d2) (LineB d2) d1 H0 H1).
	 simplLine1; canonize1.
	 simplLine1; canonize1.
Qed.

Lemma ParallelEqParallelLine : forall d1 d2 d3 : Line,
	ParallelLines d1 d2 ->
	EqLine d2 d3 ->
	ParallelLines d1 d3.
Proof.
	intros.
	inversion H0.
	destruct (EqLineOrEquiOriented d2 d3 H0).
	 destruct d1; destruct d2; destruct d3; simplLine1; canonize1.
	  right; left; intros.
	    step11 H9.
	    step11 H.
	  do 3 right; left; intros.
	    step11 H9.
	    step11 H.
	  do 2 right; left; intros.
	    step11 H2.
	    step11 H5.
	  do 7 right; intros.
	    step11 H5.
	    step11 H2.
	 destruct d1; destruct d2; destruct d3; simplLine1; canonize1.
	  left; intros.
	    step11 H2.
	   canonize1.
	   step11 H.
	  do 2 right; left; intros.
	    step11 H2.
	   canonize1.
	   step11 H.
	  do 6 right; left; intros.
	    step11 H5.
	    step11 H2.
	    left; canonize1.
	  do 7 right; intros.
	    step11 H.
	    step11 H2.
	    left; canonize1.
Qed.

Lemma EqEqParallelLine : forall d1 d2 d3 d4: Line,
	EqLine d1 d3 ->
	EqLine d2 d4 ->
	ParallelLines d1 d2 ->
	ParallelLines d3 d4.
Proof.
	intros.
	apply (ParallelEqParallelLine d3 d2 d4).
	 apply ParallelLinesSym.
	   apply (ParallelEqParallelLine d2 d1 d3).
	  apply ParallelLinesSym; immediate11.
	  immediate11.
	 immediate11.
Qed.

Lemma ParallelEqLine : forall M : Point, forall d1 d2 : Line,
	OnLine d1 M ->
	OnLine d2 M ->
	ParallelLines d1 d2 ->
	EqLine d1 d2.
Proof.
	intros.
	destruct d2.
	byApartCases3 A B M.
	 assert (EqLine (Ruler A M H2) (Ruler A B n)).
	  apply EqLineDef; immediate11.
	  apply EqLineTrans with (d2 := Ruler A M H2).
	   assert (ParallelLines d1 (Ruler A M H2)).
	    apply ParallelEqParallelLine with (d2 := Ruler A B n).
	     immediate11.
	     apply EqLineSym; immediate11.
	    destruct d1.
	      by3Cases1 A0 B0 A.
	     assert (~ EquiDirected A0 B0 A M).
	      apply FourPointsSecantLine; immediate11.
	      simplLine1.
	        elim H6; immediate11.
	     assert (~ EquiDirected B0 A0 A M).
	      apply FourPointsSecantLine; immediate11.
	      simplLine1; elim H5; immediate11.
	     apply EqLineDef; immediate11.
	   immediate11.
	 assert (EqLine (Ruler B M H2) (Ruler A B n)).
	  apply EqLineDef; immediate11.
	  apply EqLineTrans with (d2 := Ruler B M H2).
	   assert (ParallelLines d1 (Ruler B M H2)).
	    apply ParallelEqParallelLine with (d2 := Ruler A B n).
	     immediate11.
	     apply EqLineSym; immediate11.
	    destruct d1.
	      by3Cases1 A0 B0 B.
	     assert (~ EquiDirected A0 B0 B M).
	      apply FourPointsSecantLine; immediate11.
	      simplLine1; elim H6; immediate11.
	     assert (~ EquiDirected B0 A0 B M).
	      apply FourPointsSecantLine; immediate11.
	      simplLine1; elim H5; immediate11.
	     apply EqLineDef; immediate11.
	   immediate11.
Qed.

Lemma ParallelLinesDistinctLines : forall d1 d2 : Line, forall A : Point,
	ParallelLines d1 d2 ->
	OnLine d1 A ->
	~OnLine d2 A ->
	forall M : Point, ~ (OnLine d1 M /\ OnLine d2 M).
Proof.
	intros.
	contrapose0 H1.
	destruct H1; assert (EqLine d1 d2).
	 apply (ParallelEqLine M d1 d2); immediate11.
	 apply (EqLineOnLine d1 d2 A); immediate11.
Qed.

End PARALLEL_LINES.
