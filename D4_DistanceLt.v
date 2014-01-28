Require Import A1_Plan A2_Orientation A7_Tactics .
Require Import B5_BetweenProp B7_Tactics .
Require Import C1_Distance C3_SumDistance C4_DistanceLe C6_DistanceTimesN C7_Tactics .
Require Import D2_ExistsClockwise D3_SecondDimension.

Require Export Arith.

Section DISTANCE_LT.

Definition DistanceLt := fun M N : Point => DistanceLe M N /\ M <> N.

Lemma DistanceLtDistancePlus : forall A B : Point,
	Oo <> B ->
	IsDistance A ->
	DistanceLt A (DistancePlus A B).
Proof.
	intros; split.
	 immediate2.
	 since2 (Distance Oo B <> Oo).
	  contrapose0 H1.
	    apply (DistancePlusNeutralRightEq A); immediate2.
Qed.

Lemma BetweenDistanceLt : forall A B C : Point,
	Between A B C ->
	DistanceLt (Distance A B) (Distance A C).
Proof.
	intros.
	rewrite <- (Chasles A B C).
	 apply DistanceLtDistancePlus.
	  assert (H0 := BetweenDistinctBC A B C H).
	  immediate2.
	  immediate2.
	 immediate2.
Qed.

Lemma DistanceLtBetween : forall A B C : Point,
	DistanceLt (Distance A B) (Distance A C) ->
	A <> B ->
	OpenRay A B C ->
	Between A B C.
Proof.
	intros.
	destruct H.
	apply SegmentBetween.
	 apply (DistanceLeSegment A C B B); immediate2.
	 immediate2.
	 contrapose0 H2.
	   rewrite H2; immediate2.
Qed.

Lemma DistanceLeAntisym : forall A B : Point,
	A <> B ->
	DistanceLe A B ->
	~DistanceLe B A.
Proof.
	intros A B H H0 H1.
	unfold DistanceLe in *; canonize1.
	pose (C := ExistsClockwise A B H).
	assert (H5 := ClockwiseExistsClockwise A B H); fold C in H5.
	from2 H4 (Clockwise A B C).
	   step2 H0.
	   step2 H3.
	 contradict1 H1 H5.
Qed.

Lemma DistanceLeLtTrans : forall A B C : Point,
	DistanceLe A B ->
	DistanceLt B C ->
	DistanceLt A C.
Proof.
	intros A B C H (H0, H1); split.
	 apply (DistanceLeTrans A B C); immediate2.
	 intro; subst.
	   apply (DistanceLeAntisym B C H1 H0); immediate2.
Qed.

Lemma ArchimedianDistanceLt : forall A B C : Point,
	A <> B ->
	exists n : nat, n > 0 /\ DistanceLt (Distance A C) (DistanceTimes n A B).
Proof.
	intros.
	destruct (ArchimedianDistance A B C H) as (n, Hd).
	exists (S n); simpl in |- *; split.
	   auto with arith.
	apply  (DistanceLeLtTrans (Distance A C) (DistanceTimes n A B)  (DistancePlus (Distance A B) (DistanceTimes n A B))).
	 immediate2.
	 rewrite DistancePlusCommut; apply DistanceLtDistancePlus;  immediate2.
Qed.

End DISTANCE_LT.
