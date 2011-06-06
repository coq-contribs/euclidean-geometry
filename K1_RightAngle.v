Section RIGHT_ANGLE.

Definition VvDef : {Vv : Point | 
	EquiOriented Oo Vv (ExistsClockwise Uu uU DistinctUuuU) (ExistsClockwise uU Uu (sym_not_eq DistinctUuuU)) /\ 
	Distance Oo Vv = Distance Oo Uu /\ 
	Collinear (ExistsClockwise Uu uU DistinctUuuU)  (ExistsClockwise uU Uu (sym_not_eq DistinctUuuU)) Vv}.
Proof.
	pose DistinctUuuU; setMidLine9 Uu uU ipattern:yOy.
	setInterDiameterPoint5 yOy uCircle ipattern:Vv.
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
