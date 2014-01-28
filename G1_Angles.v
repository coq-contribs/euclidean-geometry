Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A6_Intersection A7_Tactics.
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B6_EquiDirectedProp B7_Tactics.
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics.
Require Import D1_IntersectionCirclesProp D2_ExistsClockwise D3_SecondDimension D4_DistanceLt D5_Tactics.
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics.
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F4_ArchimedianDistance F5_Tactics.

Section ANGLES.

Definition Angle (A B C : Point) : B <>A -> B <> C -> Point.
Proof.
	intros.
	setMarkSegmentPoint5 B A Oo Uu ipattern:D.
	setMarkSegmentPoint5 B C Oo Uu ipattern:E.
	setCircle0 Uu D E ipattern:gamma.
	setIntersectionCircles3 uCircle gamma ipattern:F.
	 simplCircle2; immediate5.
	 assert (Hts : TriangleSpec B D D E B E).
	  immediate5.
	  step5 Hts.
	 exact F.
Defined.

Ltac destructAngle A B C Hba Hbc M := 
unfold Angle at 1 in |- *; simpl in |- *;
unfold IntersectionCirclesPoint in |- *;
let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in
(destruct (InterCirclesPointDef uCircle (Compass Uu (MarkSegmentPoint B A Oo Uu Hba) (MarkSegmentPoint B C Oo Uu Hbc))) as (M, ((H1, (H2, H3)), H4));
simpl in H1, H2, H3, H4).

Lemma DistanceOoAngle : forall A B C : Point, forall Hba : B <> A, forall Hbc : B <> C,
	Distance Oo (Angle A B C Hba Hbc) = Uu.
Proof.
	intros;  destructAngle ipattern:A ipattern:B ipattern:C ipattern:Hba ipattern:Hbc  ipattern:M.
	immediate5.
Qed.

Lemma NotClockwiseAngle : forall A B C : Point, forall Hba : B <> A, forall Hbc : B <> C,
	~Clockwise Uu  (Angle A B C Hba Hbc) Oo.
Proof.
	intros; destructAngle ipattern:A ipattern:B ipattern:C ipattern:Hba ipattern:Hbc  ipattern:M.
	immediate5.
Qed.

Lemma DistanceUuAngle : forall A B C : Point, forall Hba : B <> A, forall Hbc : B <> C,
	Distance Uu (Angle A B C Hba Hbc) = Distance (MarkSegmentPoint B A Oo Uu Hba) (MarkSegmentPoint B C Oo Uu Hbc).
Proof.
	intros; destructAngle ipattern:A ipattern:B ipattern:C ipattern:Hba ipattern:Hbc  ipattern:M.
	immediate5.
Qed.

Definition IsAngle := fun M : Point => OnCircle uCircle M /\ ~Clockwise Uu M Oo. 

Lemma IsAngleDistance : forall alpha : Point,
	IsAngle alpha ->
	Distance Oo alpha = Uu.
Proof.
	intros alpha H; elim H.
	simplCircle2; intros.
	immediate5.
Qed.

Lemma IsAngleAngle :  forall A B C : Point, forall Hba : B <> A, forall Hbc : B <> C,
	IsAngle (Angle A B C Hba Hbc).
Proof.
	intros; unfold IsAngle in |- *; split.
	 simplCircle2; assert (H := DistanceOoAngle A B C Hba Hbc); immediate5.
	 apply NotClockwiseAngle.
Qed.

Lemma EqAnglePoint : forall M : Point, forall Hu : Oo <> Uu, forall Hm : Oo <> M, 
	IsAngle M ->
	Angle Uu Oo M Hu Hm = M.
Proof.
	intros M Hu Hm (Hc, Hn);  destructAngle Uu Oo ipattern:M ipattern:Hu ipattern:Hm ipattern:N.
	apply H2; intuition.
	rewrite <- (UniqueMarkSegmentPoint Oo Uu Oo Uu Hu Uu).
	 rewrite <- (UniqueMarkSegmentPoint Oo M Oo Uu Hm M).
	  immediate5.
	  immediate5.
	  immediate5.
	 immediate5.
	 immediate5.
Qed.

Lemma IsAngleDistinctOo : forall alpha : Point, 
	IsAngle alpha -> Oo <>  alpha.
Proof.
	intros.
	destruct H; simplCircle2.
	step5 H.
Qed.

Lemma EqAngle : forall alpha beta : Point,
	IsAngle alpha ->
	IsAngle beta ->
	Distance Uu alpha = Distance Uu beta ->
	alpha = beta.
Proof.
	intros.
	destruct H0.
	rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H).
	destructAngle Uu Oo alpha DistinctOoUu (IsAngleDistinctOo alpha H)  ipattern:gamma.
	apply H6; intuition.
	step5 H1.
	since5 (MarkSegmentPoint Oo Uu Oo Uu DistinctOoUu = Uu).
	since5 (MarkSegmentPoint Oo alpha Oo Uu (IsAngleDistinctOo alpha H) = alpha).
	  elim H; intros.
	    immediate5.
	  rewrite H7; rewrite H8; immediate5.
Qed.

Lemma CongruentItself : forall (A B C D E : Point) (Hab : A<>B) (Hac : A <> C) (Had : A<>D) (Hae : A <> E),
	OpenRay A B D -> OpenRay A C E ->
	Angle B A C Hab Hac = Angle  E A D Hae Had.
Proof.
	intros;  destructAngle B A C Hab Hac ipattern:alpha.
	apply H4; intuition.
	 assert (H5 := DistanceOoAngle E A D Hae Had); immediate5.
	 assert (H5 := DistanceUuAngle E A D Hae Had); step5 H5.
	   rewrite <- (UniqueMarkSegmentPoint A E Oo Uu Hae (MarkSegmentPoint A C Oo Uu Hac)).
	  rewrite <- (UniqueMarkSegmentPoint A D Oo Uu Had (MarkSegmentPoint A B Oo Uu Hab)) .
	   immediate5.
	   step5 H.
	     immediate5.
	   immediate5.
	  step5 H0.
	    immediate5.
	  immediate5.
	 elim (NotClockwiseAngle E A D Hae Had); immediate5.
Qed.

Inductive CongruentAngle (A B C D E F : Point) : Prop :=  
	| CongruentEqAngle : forall (Hba : B <> A) (Hbc : B <> C) (Hed : E  <> D) (Hef : E <> F),
		Angle A B C Hba Hbc = Angle D E F Hed Hef -> CongruentAngle A B C D E F.


Ltac applyCongruentEqAngleH3  A B C D E F H1 H2 H3 := match goal with
	| H4 : E <> F |- _ =>apply (CongruentEqAngle  A B C D E F  H1 H2 H3 H4)
	| H4 : F <> E |- _  => apply (CongruentEqAngle A B C D E F   H1 H2 H3 (sym_not_eq H4))
	| _ => let H4 := fresh in 
		(assert (H4 : E <> F);
		[try immediate5 | apply (CongruentEqAngle A B C D E F  H1 H2 H3 H4)])
end.


Ltac applyCongruentEqAngleH2  A B C D E F H1 H2 := match goal with
	| H3 : E <> D |- _ =>applyCongruentEqAngleH3  A B C D E F  H1 H2 H3
	| H3 : D <> E |- _  => applyCongruentEqAngleH3 A B C D E F   H1 H2 (sym_not_eq H3)
	| _ => let H3 := fresh in 
		(assert (H3 : E <> D);
		[try immediate5 | applyCongruentEqAngleH3 A B C D E F  H1 H2 H3])
end.

Ltac applyCongruentEqAngleH1  A B C D E F H1 := match goal with
	| H2 : B <> C |- _ =>applyCongruentEqAngleH2  A B C D E F H1 H2
	| H2 : C <> B |- _ => applyCongruentEqAngleH2 A B C D E F  H1 (sym_not_eq H2)
	| _ => let H2 := fresh in 
		(assert (H2 : B <> C);
		[try immediate5 | applyCongruentEqAngleH2 A B C D E F H1 H2])
end.

Ltac applyCongruentEqAngle := match goal with
	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => match goal with
		| H1 : B <> A |- _ => applyCongruentEqAngleH1 A B C D E F H1
		| H1 : A <> B |- _ => applyCongruentEqAngleH1 A B C D E F (sym_not_eq H1)
		| _  => let H1 := fresh in 
			(assert (H1 : B <> A);
			[try immediate5 | applyCongruentEqAngleH1  A B C D E F H1])
		end
end.

Lemma CongruentAngleDistinctBA : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	B <> A.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma CongruentAngleDistinctBC : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	B <> C.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma CongruentAngleDistinctED : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	E <> D.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma CongruentAngleDistinctEF : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	E <> F.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma CongruentAngleRefl : forall A B C : Point,
	B<>A ->
	B <> C ->
	CongruentAngle A B C A B C.
Proof.
	intros; applyCongruentEqAngle.
	immediate5.
Qed.

Lemma CongruentAngleSym : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	CongruentAngle D E F A B C.
Proof.
	intros.
	inversion H.
	applyCongruentEqAngle; immediate5.
Qed.

Lemma CongruentAngleTrans : forall A B C D E F G H J: Point,
	CongruentAngle A B C D E F ->
	CongruentAngle D E F G H J->
	CongruentAngle A B C G H J.
Proof.
	intros.
	inversion H0.
	inversion H1.
	applyCongruentEqAngle.
	rewrite H2.
	rewrite (CongruentItself E D F D F Hed Hef Hba0 Hbc0).
	 rewrite <- H3; apply CongruentItself; immediate5.
	 immediate5.
	 immediate5.
Qed.

Lemma CongruentAngleRev1 : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	CongruentAngle C B A D E F.
Proof.
	intros.
	inversion H.
	applyCongruentEqAngle; rewrite <- H0.
	apply CongruentItself; immediate5.
Qed.

Lemma CongruentAngleRev2 : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	CongruentAngle A B C F E D.
Proof.
	intros.
	apply CongruentAngleSym; apply CongruentAngleRev1; apply CongruentAngleSym; immediate5.
Qed.

Lemma CongruentAngleRev : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	CongruentAngle C B A F E D.
Proof.
	intros.
	apply CongruentAngleRev1; apply CongruentAngleRev2; immediate5.
Qed.

Lemma CongruentAnglePerm : forall A B C : Point,
	B<>A ->
	B <> C ->
	CongruentAngle A B C C B A.
Proof.
	intros.
	apply CongruentAngleRev2; apply CongruentAngleRefl; immediate5.
Qed.

Lemma EqCongruentAngle : forall (A B C D E F: Point) (Hba : B <> A) (Hbc: B <> C) (Hed : E <> D) (Hef : E <> F),
	CongruentAngle A B C D E  F ->
	Angle A B C Hba Hbc = Angle  D E F Hed Hef.
Proof.
	intros.
	assert (H0 := CongruentAngleRev _ _ _ _ _ _ H).
	inversion H0.
	apply trans_eq with (y := Angle C B A Hba0 Hbc0).
	 apply CongruentItself; immediate5.
	 rewrite H1; apply CongruentItself; immediate5.
Qed.

Lemma CongruentAngleUuOoAngle : forall A B C : Point, forall (Hba : B <> A) (Hbc : B <> C), 
	CongruentAngle A B C Uu Oo (Angle A B C Hba Hbc).
Proof.
	intros.
	assert (H := IsAngleAngle A B C Hba Hbc).
	apply  (CongruentEqAngle A B C Uu Oo (Angle A B C Hba Hbc) Hba Hbc DistinctOoUu  (IsAngleDistinctOo (Angle A B C Hba Hbc) H)).
	apply sym_eq; apply EqAnglePoint.
	exact H.
Qed.

Lemma CongruentAngleSide1 : forall A B C D : Point,
	B <> A ->
	B <> C ->
	OpenRay B A D -> 
	CongruentAngle A B C D B C.
Proof.
	intros.
	apply CongruentAngleRev1; applyCongruentEqAngle.
	 step5 H1.
	 apply CongruentItself; immediate5.
Qed.

Lemma CongruentAngleSide2 : forall A B C D : Point,
	B <> A ->
	B <> C ->
	OpenRay B C D -> 
	CongruentAngle A B C A B D.
Proof.
	intros.
	apply CongruentAngleRev1; applyCongruentEqAngle.
	 step5 H1.
	 apply CongruentItself; immediate5.
Qed.

Lemma CongruentAngleSides : forall A B C D  E: Point,
	B <> A ->
	B <> C ->
	OpenRay B A D -> 
	OpenRay B C E -> 
	CongruentAngle A B C D B E.
Proof.
	intros.
	apply (CongruentAngleTrans A B C D B C D B E).
	 apply CongruentAngleSide1; immediate5.
	 apply CongruentAngleSide2.
	  step5 H1.
	  immediate5.
	  immediate5.
Qed.

Lemma CongruentSAS : forall A B C D E F : Point,
	Distance A B = Distance D E -> 
	Distance A C = Distance D F -> 
	CongruentAngle B A C E D F ->
	Distance B C = Distance E F.
Proof.
	intros.
	inversion H1.
	generalize H2; clear H2.
	destructAngle B A C Hba Hbc ipattern:alpha.
	destructAngle E D F Hed Hef ipattern:beta.
	setMarkSegmentPoint5 A B Oo Uu ipattern:B'.
	setMarkSegmentPoint5 A C Oo Uu ipattern:C'.
	setMarkSegmentPoint5 D E Oo Uu ipattern:E'.
	setMarkSegmentPoint5 D F Oo Uu ipattern:F'.
	intro; apply DistanceEq.
	apply (EquiDistantAngle A C' B C D F' E F).
	 step5 H13.
	   step5 H12.
	 step5 H17.
	   step5 H16.
	 apply EqDistance; immediate5.
	 apply EqDistance; immediate5.
	 apply (EquiDistantAngle A B' C' B D E' F' E).
	  step5 H11.
	    step5 H10.
	  step5 H15.
	    step5 H14.
	  apply EqDistance; immediate5.
	  apply EqDistance; immediate5.
	  subst.
	    apply EqDistance; immediate5.
	  apply EqDistance; immediate5.
	 apply EqDistance; immediate5.
Qed.

Lemma CongruentSSS : forall A B C D E F : Point,
	A <> B ->
	A <> C ->
	D <> E ->
	D <> F ->
	Distance A B = Distance D E -> 
	Distance A C = Distance D F -> 
	Distance B C = Distance E F ->
	CongruentAngle B A C E D F.
Proof.
	intros A B C D E F Hab Hac Hde Hdf H H0 H1; applyCongruentEqAngle .
	destructAngle B A C Hab Hac ipattern:alpha.
	destructAngle E D F Hde Hdf ipattern:beta.
	setMarkSegmentPoint5 A B Oo Uu ipattern:B'.
	setMarkSegmentPoint5 A C Oo Uu ipattern:C'.
	setMarkSegmentPoint5 D E Oo Uu ipattern:E'.
	setMarkSegmentPoint5 D F Oo Uu ipattern:F'.
	apply H5; intuition.
	rewrite H7; apply DistanceEq.
	fold B' C' E' F' in |- *.
	apply (EquiDistantAngle D F E' F' A C B' C').
	 immediate5.
	 immediate5.
	 apply EqDistance; immediate5.
	 apply EqDistance; immediate5.
	 apply (EquiDistantAngle D E F E' A B C B').
	  immediate5.
	  immediate5.
	  apply EqDistance; immediate5.
	  apply EqDistance; immediate5.
	  apply EqDistance; immediate5.
	  apply EqDistance; immediate5.
	 apply EqDistance; immediate5.
Qed.

Lemma SumAngles : forall A B C D E : Point ,
	Clockwise A B C -> 
	Clockwise A C D -> 
	Clockwise A D E ->
	CongruentAngle B A C A C D -> 
	CongruentAngle D A E A D C ->
	Between B A E.
Proof.
	intros.
	inversion H2.
	inversion H3.
	setLine0 A B ipattern:ab.
	setCircle0 A C D ipattern:gamma.
	setInterDiameterPoint5 ab gamma ipattern:B'.
	assert (Hab' : A <> B').
	 step5 H8.
	 since5 (Distance A D = Distance C B').
	  apply (CongruentSAS C A D A C B').
	   immediate5.
	   immediate5.
	   applyCongruentEqAngle.
	     rewrite <- H4; apply CongruentItself.
	    step5 H7.
	    immediate5.
	  setLine0 A E ipattern:ae.
	    setInterDiameterPoint5 ae gamma ipattern:E'.
	    assert (Hae' : A <> E').
	   step5 H13.
	   since5 (Distance A C = Distance D E').
	    apply (CongruentSAS D A C A D E').
	     immediate5.
	     immediate5.
	     applyCongruentEqAngle.
	       rewrite <- H5.
	       rewrite (CongruentItself A D E D E Hba0 Hbc0 Hba0 Hbc0).
	      apply CongruentItself.
	       step5 H12.
	       immediate5.
	      immediate5.
	      immediate5.
	    since5 (Between B' A E').
	     apply (EquiDistantSumAngles A B' C D E').
	      step5 H7.
	      immediate5.
	      step5 H12.
	      apply EqDistance; immediate5.
	      apply EqDistance; immediate5.
	      apply EqDistance; immediate5.
	      apply EqDistance; immediate5.
	     apply (OpenRayBetween B A E' E).
	      immediate5.
	      apply BetweenSym.
	        apply (OpenRayBetween E' A B' B); immediate5.
Qed.

End ANGLES.

