Require Import A1_Plan A2_Orientation A4_Droite .
Require Import B1_ClockwiseProp B5_BetweenProp B7_Tactics .
Require Import C1_Distance C3_SumDistance C7_Tactics .
Require Import E4_Tactics .
Require Import F5_Tactics .
Require Import G1_Angles G3_ParticularAngle .
Require Import H1_Triangles .
Require Import I4_Tactics .
Require Import J1_MidLine J2_MidPoint.

Section MIDPOINTandMIDLINE_PROPERTIES.

Lemma ClockwiseAMidLineAMidPoint : forall A B : Point, forall H : A <> B,
	Clockwise A (LineA (MidLine A B H)) (MidPoint A B H).
Proof.
	intros.
	assert (H0 := MidPointBetween A B H).
	assert (H1 := ClockwiseAMidLineAB A B H).
	step8 H0.
Qed.

Lemma ClockwiseMidLineABMidPoint : forall A B : Point, forall H : A <> B,
	Clockwise (LineA (MidLine A B H)) B (MidPoint A B H).
Proof.
	intros.
	assert (H0 := MidPointBetween A B H).
	assert (H1 := ClockwiseAMidLineAB A B H).
	step8 H0.
Qed.

Lemma ClockwiseAMidLineAMidLineB : forall A B : Point, forall H : A <> B,
	Clockwise A (LineA (MidLine A B H)) (LineB (MidLine A B H)).
Proof.
	intros.
	assert (H0 := MidPointBetweenMidLine A B H).
	assert (H1 := ClockwiseAMidLineAMidPoint A B H).
	step8 H0.
Qed.

Lemma ClockwiseBMidLineBMidLineA : forall A B : Point, forall H : A <> B,
	Clockwise B (LineB (MidLine A B H)) (LineA (MidLine A B H)).
Proof.
	intros.
	assert (H0 := MidPointBetweenMidLine A B H).
	assert (H1 := MidPointBetween A B H).
	assert (H2 := ClockwiseAMidLineAB A B H).
	step8 H0.
	right; step8 H1.
Qed.

Lemma EqDistanceOnMidLine : forall A B : Point, forall H : A <> B,
forall M : Point, Distance M A = Distance M B ->
	OnLine (MidLine A B H) M.
Proof.
	intros.
	assert (H1 := ClockwiseBMidLineBMidLineA A B H).
	assert (H2 := ClockwiseAMidLineAMidLineB A B H).
	pose (C := LineA (MidLine A B H)); fold C in H1, H2.
	pose (D := LineB (MidLine A B H)); fold D in H1, H2.
	by3Cases1 C D M.
	 setFourPointsInter4 C D M B ipattern:E.
	   elim (ClockwiseNotClockwise _ _ _ H3).
	   apply ClockwiseBCA; apply (TwoSidesLine A E).
	  immediate8.
	  immediate8.
	  assert (H7 := OnMidLineEqDistance A B H E H5).
	    apply SegmentBetween.
	   apply ChaslesRec.
	     replace (Distance A M) with (Distance B M).
	    replace (Distance A E) with (Distance B E).
	     usingChasles2 B E M.
	     immediate8.
	    immediate8.
	   step8 H7.
	   immediate8.
	 setFourPointsInter4 C D A M ipattern:E.
	   elim (ClockwiseNotClockwise _ _ _ H4).
	   apply ClockwiseBCA; apply (TwoSidesLine B E).
	  immediate8.
	  immediate8.
	  assert (H7 := OnMidLineEqDistance A B H E H5).
	    apply SegmentBetween.
	   apply ChaslesRec.
	     replace (Distance B M) with (Distance A M).
	    replace (Distance B E) with (Distance A E).
	     usingChasles2 A E M.
	     immediate8.
	    immediate8.
	   step8 H7.
	   immediate8.
	 immediate8.
Qed.

Lemma UniqueMidPoint : forall (A B : Point) (H : A <> B) (J : Point),
	Collinear A B J -> Distance A J = Distance B J -> J = MidPoint A B H.
Proof.
	intros; unfold MidPoint in |- *.
	byDefEqPoint5.
	assert (H2 : OnLine (MidLine A B H) J).
	 apply EqDistanceOnMidLine; immediate8.
	 immediate8.
Qed.

Lemma MidPointRefl : forall A B : Point, forall H : A <> B, forall H' : A <> B,
	MidPoint A B H = MidPoint A B H'.
Proof.
	intros; apply UniqueMidPoint.
	 apply MidPointCollinearAB.
	 assert (H0 := MidPointEqDistance A B H); immediate8.
Qed.

Lemma MidPointSym : forall A B : Point, forall H : A <> B, forall H' : B <> A,
	MidPoint A B H = MidPoint B A H'.
Proof.
	intros; apply UniqueMidPoint.
	 assert (H0 := MidPointCollinearAB A B H); immediate8.
	 assert (H0 := MidPointEqDistance A B H); immediate8.
Qed.

Lemma MidPointUuuUOo : Oo = MidPoint Uu uU DistinctUuuU.
Proof.
	apply UniqueMidPoint.
	 assert (H := BetweenUuOouU); immediate8.
	 assert (H := DistanceOouU); immediate8.
Qed.

Lemma EquiOrientedMidLineClockwiseAB : forall A B M : Point, forall Hab : A <> B,
	EquiOriented (LineA (MidLine A B Hab)) (LineB (MidLine A B Hab)) (MidPoint A B Hab)  M ->
	Clockwise A B M.
Proof.
	intros.
	assert (H0 := MidPointBetween A B Hab).
	step8 H0.
	right; step8 H.
	 assert (H1 := MidPointOnMidLine A B Hab);  immediate8.
	 assert (H2 := ClockwiseBMidLineBMidLineA A B Hab); immediate8.
Qed.

Lemma EquiOrientedMidLineClockwiseBA : forall A B M : Point, forall Hab : A <> B,
	EquiOriented (LineB (MidLine A B Hab)) (LineA (MidLine A B Hab)) (MidPoint A B Hab)  M ->
	Clockwise A M B.
Proof.
	intros.
	assert (H0 := MidPointBetween A B Hab).
	step8 H0.
	left; step8 H.
	assert (H2 := ClockwiseBMidLineBMidLineA A B Hab); immediate8.
Qed.

Lemma TCongruentAIA'BIA' : forall A B : Point, forall Hab : A <> B,
	TCongruent (Tr A (MidPoint A B Hab) (LineA (MidLine A B Hab))) (Tr  B (MidPoint A B Hab) (LineA (MidLine A B Hab))) .
Proof.
	intros; step8 1.
	 assert (H := MidPointEqDistance A B Hab); immediate8.
	 assert (H := EquilateralAMidLineAB A B Hab); immediate8.
Qed.

Lemma TCongruentAIB'BIB' : forall A B : Point, forall Hab : A <> B,
	TCongruent  (Tr A (MidPoint A B Hab) (LineB (MidLine A B Hab)))  (Tr  B (MidPoint A B Hab) (LineB (MidLine A B Hab))) .
Proof.
	intros; step8 1.
	 assert (H := MidPointEqDistance A B Hab); immediate8.
	 assert (H := EquilateralBMidLineBA A B Hab); immediate8.
Qed.

Lemma TCongruentAIA'AIB' : forall A B : Point, forall Hab : A <> B,
	TCongruent  (Tr A (MidPoint A B Hab) (LineA (MidLine A B Hab)) )  (Tr A (MidPoint A B Hab) (LineB (MidLine A B Hab))) .
Proof.
	intros.
	assert  (TCongruent (Tr A (LineA (MidLine A B Hab)) B)  (Tr A (LineB (MidLine A B Hab)) B)).
	 step8 1.
	  step8 (Distance A B).
	   assert (H := EquilateralAMidLineAB A B Hab); immediate8.
	   assert (H := EquilateralBMidLineBA A B Hab); immediate8.
	  step8 (Distance A B).
	   assert (H := EquilateralAMidLineAB A B Hab); immediate8.
	   assert (H := EquilateralBMidLineBA A B Hab); immediate8.
	 assert (H0 := MidPointBetween A B Hab).
	   step8 2.
	  step8 H.
	  assert (CongruentAngle (LineA (MidLine A B Hab)) A (MidPoint A B Hab)  (LineA (MidLine A B Hab)) A B).
	   step8 H0.
	     assert (H1 := ClockwiseAMidLineAB A B Hab); immediate8.
	   step8 H1.
	     assert  (CongruentAngle (LineB (MidLine A B Hab)) A (MidPoint A B Hab)  (LineB (MidLine A B Hab)) A B).
	    step8 H0.
	      assert (H2 := ClockwiseBMidLineBA A B Hab); immediate8.
	    step8 H2.
	      step8 H.
Qed.

Lemma TCongruentBIA'BIB' : forall A B : Point, forall Hab : A <> B,
	TCongruent  (Tr B (MidPoint A B Hab) (LineA (MidLine A B Hab)) )  (Tr B (MidPoint A B Hab) (LineB (MidLine A B Hab))) .
Proof.
	intros.
	assert (H := TCongruentAIA'BIA' A B Hab).
	step8 H.
	assert (H0 := TCongruentAIB'BIB' A B Hab).
	step8 H0.
	apply TCongruentAIA'AIB'.
Qed.

End MIDPOINTandMIDLINE_PROPERTIES.
