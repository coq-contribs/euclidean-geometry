Require Import A1_Plan A2_Orientation A3_Metrique .
Require Import B4_RaysProp B5_BetweenProp B7_Tactics .
Require Import C1_Distance C3_SumDistance C4_DistanceLe.

Section DISTANCE_TIMES_N.

Fixpoint DistanceTimes (n:nat) (A B : Point) {struct n} : Point :=
match n with 
	| 0 => Oo
	| S p => DistancePlus (Distance A B) (DistanceTimes p A B)
end.

Lemma IsDistanceDistanceTimes : forall A B : Point, forall n : nat,
	IsDistance (DistanceTimes n A B).
Proof.
	induction n; simpl in |- *.
	 unfold IsDistance in |- *; immediate1.
	 apply IsDistanceDistancePlus.
Qed.

Lemma DistanceTimesSym : forall A B : Point, forall n : nat, 
	DistanceTimes n A B = DistanceTimes n B A.
Proof.
	induction n.
	 simpl in |- *; trivial.
	 simpl in |- *.
	   rewrite IHn.
	   rewrite (DistanceSym A B); trivial.
Qed.

Lemma ArchimedianClosedRay : forall A B M : Point,
	Archimed A B M ->
	ClosedRay A B M.
Proof.
	induction 1.
	 apply OpenRayClosedRay; apply SegmentOpenRayAC.
	   immediate1.
	 step1 H.
Qed.

Lemma ArchimedianDistance : forall A B C : Point,
	A <> B ->
	exists n : nat, DistanceLe (Distance A C) (DistanceTimes n A B).
Proof.
	intros.
	elim (EquiDistantArchimed Oo (Distance A B) (Distance A C)); intros.
	 exists 1; simpl in |- *.
	   unfold DistanceLe in |- *; rewrite DistancePlusNeutralRight.
	   rewrite EqDistanceDistance; immediate1.
	 destruct H3 as (p, H4); exists (S p); simpl in |- *.
	   replace C0 with (DistancePlus (Distance A B) D).
	  apply LeftRegularDistanceLe.
	    immediate1.
	  rewrite DistancePlusOoN; replace (Distance A B) with (Distance D C0).
	   rewrite DistancePlusCommut; rewrite Chasles.
	    apply IsDistanceEqDistance.
	      apply (EquiOrientedClosedRayClosedRay Oo Uu D).
	     step1 H0.
	       apply IsDistanceDistance.
	     apply OpenRayClosedRay; apply (OpenRayTrans Oo D (Distance A B) Uu).
	      apply ClosedRayOpenRay; apply ArchimedianClosedRay; trivial.
	      apply ClosedRayOpenRay; apply IsDistanceDistance.
	    step1 H0.
	      apply ArchimedianClosedRay; trivial.
	   rewrite <- (EqDistanceDistance A B); apply sym_eq; apply DistanceEq;
	    trivial.
	 apply OpenRayClosedRay; apply (OpenRayTrans Oo (Distance A C) Uu).
	  apply ClosedRayOpenRay; apply IsDistanceDistance.
	  apply OpenRaySym.
	   apply sym_not_eq; apply DistanceNotNull; trivial.
	   apply ClosedRayOpenRay; apply IsDistanceDistance.
Qed.

End DISTANCE_TIMES_N.

