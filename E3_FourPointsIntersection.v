Require Import A1_Plan A2_Orientation A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B5_BetweenProp B7_Tactics .
Require Import D5_Tactics .
Require Import E2_NotEquidirectedIntersection.

Section FOUR_POINTS_INTERSECTION.

Lemma ClockwiseAntiClockwiseBetween : forall A B C D E : Point,
	Clockwise A B C ->
	Clockwise B A D ->
	Collinear A B E ->
	Collinear C D E ->
	Between C E D.
Proof.
	intros.
	by3SegmentCases1 H2.
	 apply SegmentBetween.
	  trivial.
	  step3 H.
	  step3 H0.
	 elim (ClockwiseNotClockwise _ _ _ H0).
	   by3SegmentCases1 H1; canonize1.
	  step3 H4; step3 H8; step3 H4.
	   intro; subst.
	     elim (ClockwiseNotClockwise _ _ _ H).
	     step3 H8.
	  step3 H4; step3 H8; step3 H4.
	  step3 H9; step3 H8; step3 H9.
	 elim (ClockwiseNotClockwise _ _ _ H0).
	   by3SegmentCases1 H1; canonize1.
	  step3 H4; step3 H2.
	   step3 H0.
	   step3 H4.
	    intro; subst.
	      elim (ClockwiseNotClockwise _ _ _ H).
	      step3 H3.
	  step3 H4; step3 H2.
	   step3 H0.
	   step3 H4.
	  step3 H9; step3 H2.
	   step3 H0.
	   step3 H9.
Qed.

Definition FourPointsInterPoint : forall A B C D,
	Clockwise A B C -> Clockwise B A D -> Point.
Proof.
	intros.
	apply (NotEquiDirectedInterPoint A B C D).
	apply FourPointsSecantLine; immediate3.
Defined.

Lemma FourPointsInterPointCollinearAB : forall (A B C D : Point) (H : Clockwise A B C) (H0 : Clockwise B A D),
	Collinear A B  (FourPointsInterPoint A B C D H H0).
Proof.
	intros; unfold FourPointsInterPoint in |- *.
	apply NotEquiDirectedInterPointCollinearAB.
Qed.

Lemma FourPointsInterPointBetweenCD : forall (A B C D : Point) (H : Clockwise A B C) (H0 : Clockwise B A D),
	Between C (FourPointsInterPoint A B C D H H0) D.
Proof.
	intros; unfold FourPointsInterPoint in |- *.
	apply (ClockwiseAntiClockwiseBetween A B C D).
	 trivial.
	 trivial.
	 apply NotEquiDirectedInterPointCollinearAB.
	 apply NotEquiDirectedInterPointCollinearCD.
Qed.

Lemma UniqueFourPointsInterPoint: forall (A B C D : Point) (H : Clockwise A B C) (H0 : Clockwise B A D), forall M : Point,
	Collinear A B M ->
	Collinear C D M ->
	M = FourPointsInterPoint A B C D H H0.
Proof.
	intros; unfold FourPointsInterPoint in |- *.
	apply UniqueNotEquiDirectedInterPoint; immediate3.
Qed.

Lemma PaschABC  : forall A B C M N,
	Clockwise A B C -> Between A M B  -> ~Collinear A M N ->
	~Collinear B M N -> ~Collinear C M N ->
	(exists P : Point, Collinear M N P /\ Between A P C) \/
	(exists P : Point, Collinear M N P /\ Between B P C).
Proof.
	intros A B C M N H (H0, H1) H2 H3 H4.
	by2Cases1 H2; by2Cases1 H3.
	 clear H2 H3 H4; elim (ClockwiseNotClockwise B M N); canonize1.
	 by2Cases1 H4; clear H2 H3 H4.
	  since3 (Clockwise N M B).	
	    since3 (Clockwise M N C).
	    pose (P := FourPointsInterPoint N M B C H2 H3).
	    right; exists P; split.
	   apply CollinearBAC; unfold P in |- *;
	    apply FourPointsInterPointCollinearAB.
	   unfold P in |- *; apply FourPointsInterPointBetweenCD.
	  since3 (Clockwise M N A).
	    since3 (Clockwise N M C).
	    pose (P := FourPointsInterPoint M N A C H2 H3).
	    left; exists P; split.
	   unfold P in |- *; apply FourPointsInterPointCollinearAB.
	   unfold P in |- *; apply FourPointsInterPointBetweenCD.
	 by2Cases1 H4; clear H2 H3 H4.
	  since3 (Clockwise N M A).
	    since3 (Clockwise M N C).
	    pose (P := FourPointsInterPoint N M A C H2 H3).
	    left; exists P; split.
	   apply CollinearBAC; unfold P in |- *;
	    apply FourPointsInterPointCollinearAB.
	   unfold P in |- *; apply FourPointsInterPointBetweenCD.
	  since3 (Clockwise M N B).
	    since3 (Clockwise N M C).
	    pose (P := FourPointsInterPoint M N B C H2 H3).
	    right; exists P; split.
	   unfold P in |- *; apply FourPointsInterPointCollinearAB.
	   unfold P in |- *; apply FourPointsInterPointBetweenCD.
	 clear H2 H3 H4; elim (ClockwiseNotClockwise B M N); canonize1.
	   step3 H1.
Qed.

End FOUR_POINTS_INTERSECTION.

