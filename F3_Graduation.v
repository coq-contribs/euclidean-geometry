Require Import A1_Plan A2_Orientation .
Require Import B2_CollinearProp B4_RaysProp B5_BetweenProp .
Require Import C1_Distance .
Require Import D3_SecondDimension .
Require Import E4_Tactics .
Require Import F2_MarkSegment.

Require Export Omega.

Section GRADUATION.

Definition GraduationSpec : forall A B : Point, forall Hab : A <> B, forall n : nat, {M : Point | Collinear A B M}.
Proof.
	intros; induction n.
	 exists A; apply CollinearABA.
	 destruct IHn as (An, Hn).
	   exists (AddSegmentPoint A B An A B Hab Hn).
	   assert (H := EquiOrientedAddSegmentPoint A B An A B Hab Hn).
	   apply CollinearBCA; apply (EquiOrientedCollinearACDCollinearBCD An).
	  exact H.
	  apply CollinearCAB; exact Hn.
Defined.

Definition Graduation (n : nat) (A B : Point) (Hab : A <> B) := let (An, _) := GraduationSpec A B Hab n in An.

Lemma Graduation0 : forall A B : Point, forall Hab : A <> B, 
	Graduation 0 A B Hab = A.
Proof.
	intros; unfold Graduation in |- *.
	 simpl in |- *; trivial.
Qed.

Lemma Graduation1 : forall A B : Point, forall Hab : A <> B, 
	Graduation 1 A B Hab = B.
Proof.
	intros; unfold Graduation in |- *; simpl in |- *.
	apply sym_eq; apply UniqueAddSegmentPoint; immediate4.
Qed.

Lemma CollinearGraduation : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Collinear A B (Graduation n A B Hab).
Proof.
	intros; unfold Graduation in |- *; simpl in |- *.
	destruct (GraduationSpec A B Hab n) as (An, Hn).
	trivial.
Qed.

Lemma EqDistanceGraduation : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Distance (Graduation n A B Hab) (Graduation (S n) A B Hab) = Distance A B.
Proof.
	intros; unfold Graduation in |- *; simpl in |- *.
	destruct (GraduationSpec A B Hab n) as (An, Hn).
	apply EqDistanceAddSegmentPoint.
Qed.

Lemma EquiOrientedGraduation : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	EquiOriented (Graduation n A B Hab) (Graduation (S n) A B Hab) A B.
Proof.
	intros; unfold Graduation in |- *; simpl in |- *.
	destruct (GraduationSpec A B Hab n) as (An, Hn).
	apply EquiOrientedAddSegmentPoint.
Qed.

Lemma GraduationSn : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Graduation (S n) A B Hab = AddSegmentPoint A B (Graduation n A B Hab) A B Hab (CollinearGraduation n A B Hab).
Proof.
	intros.
	apply UniqueAddSegmentPoint.
	   apply EquiOrientedGraduation.
	   apply EqDistanceGraduation.
Qed.

Lemma GraduationDistinctnSn : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Graduation n A B Hab <> Graduation (S n) A B Hab.
Proof.
	intros.
	assert (H0 := EqDistanceGraduation n A B Hab).
	step4 H0.
Qed.

Lemma GraduationBetweennSnSSn : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Between (Graduation n A B Hab) (Graduation (S n) A B Hab) (Graduation (S (S n)) A B Hab).
Proof.
	intros; split.
	 apply GraduationDistinctnSn.
	 assert (H := EquiOrientedGraduation n A B Hab);
	  assert (H0 := EquiOrientedGraduation (S n) A B Hab).
	   step4 H.
	   step4 H0.
	  apply GraduationDistinctnSn.
	  right; assert (H1 := CollinearGraduation (S (S n)) A B Hab); immediate4.
Qed.

Lemma GraduationClosedRay : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	ClosedRay A B (Graduation n A B Hab).
Proof.
	intros; induction n.
	 rewrite Graduation0; immediate4.
	 apply (EquiOrientedClosedRayClosedRay A B (Graduation n A B Hab)).
	  apply EquiOrientedGraduation.
	  trivial.
Qed.

Lemma GraduationSegment : forall n : nat, forall A B : Point, forall Hab : A <> B, 
	Segment A (Graduation (S n) A B Hab) (Graduation n A B Hab).
Proof.
	intros.
	apply (EquiOrientedClosedRaySegment A B).
	 apply EquiOrientedGraduation.
	 apply GraduationClosedRay.
Qed.

End GRADUATION.

