Require Import A1_Plan A2_Orientation A4_Droite .
Require Import B7_Tactics .
Require Import D5_Tactics .
Require Import I2_Supplement .
Require Import L2_StrictParallelogramm L6_Tactics .
Require Import M1_SuperImposedLines M5_Tactics .
Require Import N2_DrawingParallelLine.

Section PARALLEL_OPPOSED_LINES.

Lemma TwoPointsOnParallel : forall d : Line, forall C : Point, forall H : ~OnLine d C,
	Clockwise (LineA d) (LineB d) C ->
	exists D : Point, exists E : Point, 
		StrictParallelogramm (LineA d) (LineB d) C D /\ StrictParallelogramm C (LineA d) (LineB d) E /\
		Between D C E /\ OnLine (Parallel d C H) D /\ OnLine (Parallel d C H) E.
Proof.
	intros.
	setStrictParallelogramm11 (LineA d) (LineB d) C ipattern:(D).
	exists D.
	setStrictParallelogramm11 C (LineA d) (LineB d) ipattern:(E).
	exists E.
	assert (Between D C E).
	apply (TriangleBetween (LineA d) C (LineB d) C D (LineA d) (LineB d) E); immediate12.
	split; [ immediate12 | idtac ].
	split; [ immediate12 | idtac ].
	 split; [immediate12 | idtac].
	  assert (OnLine (Parallel d C H) D).
	   unfold D in |- *; rewrite <- (OnParallelVertexP4 d C H).
	     immediate12.
	 split; [immediate12 | idtac].
	    since3 (C <> D).
	      since3 (EqLine (Parallel d C H) (Ruler C D H5)).
	     step12 (C,D).
	       apply OnLineAParallel.
	     step12 H6.
Qed.

Lemma EqParallelOppLines : forall A B C : Point, forall (Hab : A <> B), forall (Hba : B <> A),
forall (H1 : ~OnLine (Ruler A B Hab) C), forall (H2 : ~OnLine (Ruler B A Hba) C),
	EqLine (Parallel (Ruler A B Hab) C H1) (Parallel (Ruler B A Hba) C H2).
Proof.
	intros.
	since12 (~ Collinear A B C).
	by2Cases1 H.
	
	 destruct (TwoPointsOnParallel (Ruler A B Hab) C H1) as (D, (E, (H3, (H4, (H5, (H6, H7)))))).
	  immediate12.
	  since12 (Clockwise C (LineB (Ruler B A Hba)) (LineA (Ruler B A Hba))).
	    since12 (E = LineB (Parallel (Ruler B A Hba) C H2)).
	   rewrite (OnParallelOppVertexP4 (Ruler B A Hba) C H2 H8).
	     step12 E.
	   step12 (C, E).
	    apply OnLineAParallel.
	    apply OnLineAParallel.
	    rewrite H9; immediate12.
	
	 destruct (TwoPointsOnParallel (Ruler B A Hba) C H2) as (D, (E, (H3, (H4, (H5, (H6, H7)))))).
	  immediate12.
	  since12 (Clockwise C (LineB (Ruler A B Hab)) (LineA (Ruler A B Hab))).
	    since12 (E = LineB (Parallel (Ruler A B Hab) C H1)).
	   rewrite (OnParallelOppVertexP4 (Ruler A B Hab) C H1 H8).
	     step12 E.
	   step12 (C, E).
	    apply OnLineAParallel.
	    apply OnLineAParallel.
	    rewrite H9; immediate12.
Qed.

End PARALLEL_OPPOSED_LINES.
