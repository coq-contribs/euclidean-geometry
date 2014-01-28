Require Import A1_Plan A2_Orientation .
Require Import B5_BetweenProp .
Require Import C1_Distance C3_SumDistance C6_DistanceTimesN C7_Tactics .
Require Import E4_Tactics .
Require Import F3_Graduation.

Section ARCHIMEDIAN_DISTANCE.

Lemma GraduationSegmentSn : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Segment A (Graduation (S n) A B Hab) B.
Proof.
	intros; induction n.
	 rewrite Graduation1; immediate4.
	 apply (SegmentTransADB A B (Graduation (S n) A B Hab)).
	  trivial.
	  apply GraduationSegment.
Qed.

Lemma GraduationBetweenAnSn : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	n >= 1 ->
	Between A (Graduation n A B Hab) (Graduation (S n) A B Hab).
Proof.
	intros.
	induction H.
	 apply SegmentBetween.
	  rewrite Graduation1; apply GraduationSegmentSn.
	  rewrite Graduation1; immediate4.
	  apply GraduationDistinctnSn.
	 step4 IHle.
	  apply GraduationBetweennSnSSn.
Qed.

Lemma GraduationSegmentB : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Segment B (Graduation (S (S n)) A B Hab) (Graduation (S n) A B Hab).
Proof.
	intros.
	apply (SegmentTransBDC A).
	 apply GraduationSegmentSn.
	 apply GraduationSegment.
Qed.

Lemma GraduationEqDistance : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Distance A (Graduation n A B Hab) = Distance B (Graduation (S n) A B Hab).
Proof.
	intros; induction n.
	 rewrite Graduation0; rewrite Graduation1; immediate4.
	 usingChasles2 A (Graduation n A B Hab) (Graduation (S n) A B Hab).
	  usingChasles2 B (Graduation (S n) A B Hab) (Graduation (S (S n)) A B Hab).
	   repeat rewrite EqDistanceGraduation.
	     immediate4.
	   apply GraduationSegmentB.
	  apply GraduationSegment.
Qed.

Lemma DistanceGraduation : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Distance A (Graduation n A B Hab) = DistanceTimes n A B.
Proof.
	intros; induction n.
	 rewrite Graduation0; simpl in |- *; immediate4.
	 usingChasles2 A (Graduation n A B Hab) (Graduation (S n) A B Hab).
	  rewrite EqDistanceGraduation; simpl in |- *.
	    rewrite IHn; apply DistancePlusCommut.
	  apply GraduationSegment.
Qed.

End ARCHIMEDIAN_DISTANCE.

