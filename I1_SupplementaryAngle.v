Require Import A1_Plan
A2_Orientation
A3_Metrique
A4_Droite
A5_Cercle
A6_Intersection
A7_Tactics
B1_ClockwiseProp
B2_CollinearProp
B3_EquiOrientedProp
B4_RaysProp
B5_BetweenProp
B6_EquiDirectedProp
B7_Tactics
C1_Distance
C2_CircleAndDistance
C3_SumDistance
C4_DistanceLe
C5_TriangularInequality
C6_DistanceTimesN
C7_Tactics
D1_IntersectionCirclesProp
D2_ExistsClockwise
D3_SecondDimension
D4_DistanceLt
D5_Tactics
E1_IntersectionLinesProp
E2_NotEquidirectedIntersection
E3_FourPointsIntersection
E4_Tactics
F1_IntersectionDiameterProp
F2_MarkSegment
F3_Graduation
F4_ArchimedianDistance
F5_Tactics
G1_Angles
G2_AngleProp
G3_ParticularAngle
G4_Tactics
H1_Triangles
H2_ParticularTriangles
H3_BuildingTriangle
H4_Tactics.

Section SUPPLEMENTARY_ANGLE.

Definition Supplementary : forall alpha : Point, forall H : IsAngle alpha, Point.
Proof.
	intros.
	setAngle6 alpha Oo uU ipattern:(beta).
	  immediate6.
	  immediate6.
	 exact beta.
Defined.

Lemma IsAngleSupplementary : forall alpha : Point, forall H : IsAngle alpha, 
	IsAngle (Supplementary alpha H).
Proof.
	intros; unfold Supplementary in |- *; immediate6.
Qed.

Lemma EqDistanceUuSupplementary : forall alpha : Point, forall H : IsAngle alpha,
	 Distance uU alpha = Distance Uu (Supplementary alpha H).
Proof.
	intros; unfold Supplementary in |- *.
	rewrite DistanceUuAngle.
	since7 (MarkSegmentPoint Oo alpha Oo Uu (IsAngleDistinctOo alpha H) = alpha).
	 since7 (MarkSegmentPoint Oo uU Oo Uu DistinctOouU = uU).
	  rewrite H0; rewrite H1; immediate7.
Qed.

Lemma SupplementaryEqAngles : forall alpha beta : Point, forall Ha : IsAngle alpha, forall Hb : IsAngle beta,
	alpha = beta ->
	Supplementary alpha Ha = Supplementary beta Hb.
Proof.
	intros; unfold Supplementary in |- *.
	eqToCongruent6.
	rewrite H; immediate7.
Qed.

Lemma SupplementaryNullAngle : forall H : IsAngle Uu,
	Supplementary Uu H = uU.
Proof.
	intros; unfold Supplementary in |- *.
	apply EqAnglePoint; immediate7.
Qed.

Lemma SupplementaryElongatedAngle : forall H : IsAngle uU,
	Supplementary uU H = Uu.
Proof.
	intros; unfold Supplementary in |- *.
	immediate7.
Qed.

Lemma OnLineOoUuIsAngle : forall alpha : Point,
	OnLine lineOoUu alpha ->
	IsAngle alpha ->
	alpha = uU \/ alpha = Uu.
Proof.
	intros.
	destruct (TwoPointsOnLineOrientation Oo alpha lineOoUu).
	 immediate7.
	 immediate7.
	 simpl in H1; right.
	   setInterDiameter lineOoUu uCircle ipattern:(beta).
	   apply trans_eq with (y := beta).
	  apply sym_eq; apply Hun; split; immediate7.
	  apply Hun; split; immediate7.
	 simpl in H1; left; step7 uU.
	  immediate7.
	    immediate7.
	  immediate7.
Qed.

Lemma ClockwiseSupplementarySupplementary : forall alpha : Point, forall H : IsAngle alpha, forall HH : IsAngle (Supplementary alpha H),
	Clockwise Uu Oo alpha ->
	Supplementary (Supplementary alpha H) HH = alpha.
Proof.
	intros alpha H; pose (beta := Supplementary alpha H).
	assert (H0 := EqDistanceUuSupplementary alpha H).
	fold beta in H0 |- *; intros.
	since7 (TCongruent (Tr alpha Oo uU) (Tr beta Oo Uu)).
	 since7 (TCongruent (Tr alpha Uu uU) (Tr beta uU Uu)).
	  step7 4.
	    assert (H4 := BetweenUuOouU).
	    since7 (uU <> alpha).
	   intro H5; rewrite <- H5 in H1.
	     contradict1 H1 H4.
	   from7 H0 (Uu <> beta).
	    from7 H4 (CongruentAngle Uu uU alpha Oo uU alpha).
	     step6 H6.
	       from7 H4 (CongruentAngle uU Uu beta Oo Uu beta).
	      step6 H7.
	        step7 H2.
	  since7 (TCongruent (Tr beta Oo uU) (Tr alpha Oo Uu)).
	   step7 1.
	     step7 H3.
	   unfold Supplementary in |- *.
 	    step7 alpha.
Qed.

Lemma SupplementarySupplementary : forall alpha : Point, forall H : IsAngle alpha, forall HH : IsAngle (Supplementary alpha H),
	Supplementary (Supplementary alpha H) HH = alpha.
Proof.
	intros.
	by3Cases1 Oo Uu alpha.
	 elim H; intros.
	   elim H2; immediate7.
	 apply ClockwiseSupplementarySupplementary; immediate7.
	 destruct (OnLineOoUuIsAngle alpha).
	  immediate7.
	  immediate7.
	  subst.
	    generalize HH.
	    rewrite SupplementaryElongatedAngle.
	    exact SupplementaryNullAngle.
	  subst.
	    generalize HH.
	    rewrite SupplementaryNullAngle.
	    exact SupplementaryElongatedAngle.
Qed.

Lemma SupplementarySym : forall alpha beta : Point, forall Ha : IsAngle alpha, forall Hb : IsAngle beta,
	beta = Supplementary alpha Ha ->
	alpha = Supplementary beta Hb .
Proof.
	intros.
	generalize Hb; clear Hb.
	rewrite H.
	intro; rewrite SupplementarySupplementary.
	immediate7.
Qed.

End SUPPLEMENTARY_ANGLE.
