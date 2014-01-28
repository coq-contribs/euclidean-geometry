Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import B1_ClockwiseProp B7_Tactics .
Require Import C1_Distance .
Require Import E3_FourPointsIntersection .
Require Import F5_Tactics .
Require Import I4_Tactics .
Require Import J1_MidLine.

Section MIDPOINT.

Definition MidPoint := fun (A B : Point) (H : A <> B) =>
FourPointsInterPoint A B (LineB (MidLine A B H)) (LineA (MidLine A B H)) 
(ClockwiseCAB B (LineB (MidLine A B H)) A (ClockwiseBMidLineBA A B H))
(ClockwiseCAB A (LineA (MidLine A B H)) B (ClockwiseAMidLineAB A B H)).

Lemma MidPointOnMidLine : forall A B : Point, forall H : A <> B,
	OnLine (MidLine A B H) (MidPoint A B H).
Proof.
	intros; unfold MidPoint in |- *; simplLine1.
	immediate8.
Qed.

Lemma MidPointEqDistance : forall (A B : Point) (H : A <> B), 
	Distance A (MidPoint A B H) = Distance (MidPoint A B H) B.
Proof.
	intros.
	assert (H0 := OnMidLineEqDistance A B H (MidPoint A B H) (MidPointOnMidLine A B H)).
	immediate8.
Qed.

Lemma MidPointBetweenMidLine : forall (A B : Point) (H : A <> B), 
	Between (LineA (MidLine A B H)) (MidPoint A B H) (LineB (MidLine A B H)).
Proof.
	intros; unfold MidPoint in |- *; simplLine1.
	immediate8.
Qed.

Lemma MidPointDistinctMidLineA : forall (A B : Point) (H : A <> B), 
	MidPoint A B H <> LineA (MidLine A B H).
Proof.
	intros; assert (H0 := MidPointBetweenMidLine A B H).
	immediate8.
Qed.

Lemma MidPointDistinctMidLineB : forall (A B : Point) (H : A <> B), 
	MidPoint A B H <> LineB (MidLine A B H).
Proof.
	intros; assert (H0 := MidPointBetweenMidLine A B H).
	immediate8.
Qed.

Lemma MidPointCollinearAB : forall (A B : Point) (H : A <> B), 
	Collinear A B (MidPoint A B H).
Proof.
	intros; unfold MidPoint in |- *; simplLine1.
	immediate8.
Qed.

Lemma DistinctMidPointA : forall (A B : Point) (H : A <> B),
	MidPoint A B H <> A.
Proof.
	intros.
	intro; elim H.
	assert (H1 := MidPointEqDistance A B H).
	rewrite H0 in H1.
	immediate8.
Qed.

Lemma DistinctMidPointB : forall (A B : Point) (H : A <> B),
	MidPoint A B H <> B.
Proof.
	intros.
	intro; elim H.
	assert (H1 := MidPointEqDistance A B H).
	rewrite H0 in H1.
	immediate8.
Qed.

Lemma MidPointBetween : forall (A B : Point) (H : A <> B), 
	Between A (MidPoint A B H) B.
Proof.
	intros.
	assert (H0 := MidPointCollinearAB A B H).
	assert (H1 := DistinctMidPointA A B H).
	assert (H2 := DistinctMidPointB A B H).
	assert (H3 := MidPointEqDistance A B H).
	by3SegmentCases1 H0.
	 step8 H4.
	 elim H.
	   setMarkSegmentPoint5 (MidPoint A B H) B (MidPoint A B H) B ipattern:C.
	   step8 C.
	 elim H.
	   setMarkSegmentPoint5 (MidPoint A B H) A (MidPoint A B H) A ipattern:C.
	   step8 C.
Qed.

End MIDPOINT.
