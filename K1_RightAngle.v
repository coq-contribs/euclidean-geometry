Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A6_Intersection A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B6_EquiDirectedProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D2_ExistsClockwise D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics .
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F4_ArchimedianDistance F5_Tactics .
Require Import G1_Angles G2_AngleProp G3_ParticularAngle G4_Tactics .
Require Import H1_Triangles H2_ParticularTriangles H3_BuildingTriangle H4_Tactics .
Require Import I1_SupplementaryAngle I2_Supplement I3_OpposedAngles I4_Tactics .
Require Import J1_MidLine J2_MidPoint J3_MidProp J4_Tactics.

Section RIGHT_ANGLE.

Definition VvDef : {Vv : Point | 
	EquiOriented Oo Vv (ExistsClockwise Uu uU DistinctUuuU) (ExistsClockwise uU Uu (sym_not_eq DistinctUuuU)) /\ 
	Distance Oo Vv = Distance Oo Uu /\ 
	Collinear (ExistsClockwise Uu uU DistinctUuuU)  (ExistsClockwise uU Uu (sym_not_eq DistinctUuuU)) Vv}.
Proof.
	pose DistinctUuuU; setMidLine9 Uu uU ipattern:(yOy).
	setInterDiameterPoint5 yOy uCircle ipattern:(Vv).
	 assert (H2 : OnLine yOy Oo).
	  step9 yOy; immediate9.
	  immediate9.
	 exists Vv; intuition.
Defined.

Definition Vv := let (M,_) := VvDef in M.

Ltac destructVv := unfold Vv in |- *;
	let M := fresh in let H1 := fresh "H" in  let H2 := fresh "H" in  let H3 := fresh "H" in destruct VvDef as (M, (H1, (H2, H3)));
	simpl in *.

Lemma DistanceOoVv : Distance Oo Vv = Uu.
Proof.
	destructVv; immediate9.
Qed.

Lemma OnMidLineVv : OnLine (MidLine Uu uU DistinctUuuU) Vv.
Proof.
	destructVv; immediate9.
Qed.

Lemma ClockwiseuUVvUu : Clockwise uU Vv Uu.
Proof.
	step9 OnMidLineVv.
	destructVv.
	step9 H0.
	 step9 H1.
	 replace Oo with (MidPoint Uu uU DistinctUuuU); immediate9.
Qed.

Lemma ClockwiseOoVvUu : Clockwise Oo Vv Uu.
Proof.
	   step9 BetweenUuOouU.
	   left; assert (H := ClockwiseuUVvUu); immediate9.
Qed.
	
Lemma DistinctOoVv : Oo <> Vv.
Proof.
	assert (H := DistanceOoVv).
	step9 H.
Qed.

Lemma EqDistanceVvUuuU : Distance Vv Uu = Distance Vv uU.
Proof.
	assert (H := OnMidLineVv).
	step9 H.
Qed.

Lemma EqVv : forall M : Point,
	Distance Oo M = Uu -> ~Clockwise Uu M uU -> Distance M Uu = Distance M uU ->
	M = Vv.
Proof.	
	intros; unfold Vv, VvDef in |- *.
	byDefEqPoint9.
	simplCircle2; pose (l := MidLine Uu uU DistinctUuuU); fold l in |- *.
	destruct (TwoPointsOnLineOrientation Oo M l).
	 step9 l; immediate9.
	 step9 l; immediate9.
	 immediate9.
	 elim H0; unfold l in H2.
	   step9 H2.
	   replace (MidPoint Uu uU DistinctUuuU) with Oo.
	  step9 H2.
	   step9 H.
	   right; from9  l   (OnLine l M).
	    step9 H3.
	  immediate9.
Qed.

Lemma DistinctUuVv : Uu <> Vv.
Proof.
	assert (H := ClockwiseuUVvUu); immediate9.
Qed.

Lemma DistinctuUVv : uU <> Vv.
Proof.
	assert (H := ClockwiseuUVvUu); immediate9.
Qed.

Lemma IsAngleVv : IsAngle Vv.
Proof.
	generalize ClockwiseOoVvUu.
	destructVv; split;  immediate9.
Qed.

Definition RightAngle ( A B C : Point)  := CongruentAngle A B C Uu Oo Vv.

Lemma RightUuOoVv : RightAngle Uu Oo Vv.
Proof.
	unfold RightAngle in |- *.
	step9 Oo.
	exact DistinctOoVv.
Qed.

Lemma RightVvOouU : RightAngle Vv Oo uU.
Proof.
	assert (H := DistinctOoVv); assert (H0 := EqDistanceVvUuuU).
	from9 1 (TCongruent (Tr Vv Oo uU) (Tr Vv Oo Uu)).
	 unfold RightAngle in |- *; step9 H.
Qed.

Lemma RightAngleSym : forall A B C : Point,
	RightAngle A B C ->
	RightAngle C B A.
Proof.
	unfold RightAngle in |- *; intros.
	immediate9.
Qed.

Lemma RightAngleDistinctBA : forall A B C : Point,
	RightAngle A B C ->
	B <> A.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma RightAngleDistinctBC : forall A B C : Point,
	RightAngle A B C ->
	B <> C.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma CongruentRightAngle : forall A B C D E F : Point,
	RightAngle A B C ->
	CongruentAngle A B C D E F ->
	RightAngle D E F.
Proof.
	unfold RightAngle in |- *; intros.
	step9 H0.
Qed.

Lemma RightCongruentAngle : forall A B C D E F : Point,
	RightAngle A B C ->
	RightAngle D E F ->
	CongruentAngle A B C D E F.
Proof.
	unfold RightAngle in |- *; intros.
	step9 H0.
Qed.

Lemma RightEqAngleVv : forall A B C  : Point, forall Hba : B <> A, forall Hbc : B <> C,
	RightAngle A B C ->
	Angle A B C Hba Hbc = Vv.
Proof.
	unfold RightAngle in |- *; intros.
	assert (H0 := IsAngleVv).
	step9 H0.
Qed.

Lemma AngleVvEqRight : forall A B C  : Point, forall Hba : B <> A, forall Hbc : B <> C,
	Angle A B C Hba Hbc = Vv ->
	RightAngle A B C.
Proof.
	unfold RightAngle in |- *; intros.
	congruentToEq8.
	 exact DistinctOoVv.
	 rewrite H.
	   assert (H2 := IsAngleVv).
	   step9 H2.
Qed.

Lemma RightAngleNotNullAngle : forall A B C : Point,
	RightAngle A B C -> ~NullAngle A B C.
Proof.
	intros; intro.
	inversion H; inversion H0.
	elim DistinctUuVv.
	rewrite <- (RightEqAngleVv A B C Hba Hbc H).
	immediate9.
Qed.

Lemma NullAngleNotRightAngle : forall A B C : Point,
	NullAngle A B C -> ~RightAngle A B C.
Proof.
	intros; intro.
	inversion H; inversion H0.
	elim DistinctUuVv.
	rewrite <- (RightEqAngleVv A B C Hba0 Hbc0 H0).
	immediate9.
Qed.

Lemma RightAngleNotElongatedAngle : forall A B C : Point,
	RightAngle A B C -> ~ElongatedAngle A B C.
Proof.
	intros; intro.
	inversion H; inversion H0.
	elim DistinctuUVv.
	rewrite <- (RightEqAngleVv A B C Hba Hbc H).
	immediate9.
Qed.

Lemma ElongatedAngleNotRightAngle : forall A B C : Point,
	ElongatedAngle A B C -> ~RightAngle A B C.
Proof.
	intros; intro.
	inversion H; inversion H0.
	elim DistinctuUVv.
	rewrite <- (RightEqAngleVv A B C Hba0 Hbc0 H0).
	immediate9.
Qed.

End RIGHT_ANGLE.
