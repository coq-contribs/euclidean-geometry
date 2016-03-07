Require Import A1_Plan A2_Orientation .
Require Import B7_Tactics .
Require Import C1_Distance C6_DistanceTimesN C7_Tactics .
Require Import D4_DistanceLt .
Require Import F3_Graduation F4_ArchimedianDistance F5_Tactics .
Require Import G1_Angles .
Require Import H1_Triangles .
Require Import I2_Supplement .
Require Import L2_StrictParallelogramm L6_Tactics .
Require Import M5_Tactics.

Section DISCRETE_THALES.

Lemma DThales : forall (A B C : Point) (Hab : A <> B) (Hac : A <> C) (Habc : Clockwise A B C) (n : nat),
	n > 0 ->
	Clockwise A (Graduation n A B Hab) (Graduation n A C Hac) /\
	CongruentAngle A B C A (Graduation n A B Hab) (Graduation n A C Hac) /\
	CongruentAngle A C B A (Graduation n A C Hac) (Graduation n A B Hab)  /\
	Distance (Graduation n A B Hab) (Graduation n A C Hac) = DistanceTimes n B C.
Proof.
	intros.
	induction H.

	 repeat rewrite Graduation1; simpl in |- *; repeat split; immediate12.

	 setGraduationPoint5 m A B ipattern:(Bm); fold Bm in IHle.
	   setGraduationPoint5 m A C ipattern:(Cm); fold Cm in IHle.
	   decompose [and] IHle; clear IHle.
	   setGraduationPoint5 (S m) A B ipattern:(Bsm); fold Bsm in |- *.
	   setGraduationPoint5 (S m) A C ipattern:(Csm); fold Csm in |- *.
	   since12 (Between A Bm Bsm).
	  unfold Bm, Bsm in |- *; apply GraduationBetweenAnSn; immediate12.
	  from12 H12 (Clockwise Cm Bm Bsm).
	    setStrictParallelogramm11 Cm Bm Bsm ipattern:(D).
	    DestructSP11 H14.
	    from12 H15 (CongruentAngle D Bsm Bm Cm Bm A).
	    from12 2 (TCongruent (Tr A B C) (Tr Cm D Csm)).
	   unfold Cm, Csm in |- *; immediate12.
	   as12 (Distance Cm D = Distance Bm Bsm).
	     unfold Bm, Bsm in |- *; immediate12.
	   since12 (Between A Cm Csm).
	    unfold Cm, Csm in |- *; apply GraduationBetweenAnSn; immediate12.
	    as12 (Supplement Csm Cm D D Cm A).
	     immediate12.
	     apply SupplementRev1; apply SupplementRev2; apply SupplementSym; apply (TriangleSumSupplement C B A Cm A Bm D).
	      step12 H0.
	        step12 H2.
	      immediate12.
	      immediate12.
	      step12 H6.
	        step12 H15.
	   since12 (Clockwise Cm D Csm).
	    apply (TriangleSumClockwise C B A Cm A Bm D Csm).
	     immediate12.
	     immediate12.
	     immediate12.
	     step12 H6.
	       step12 H15.
	     unfold Cm, Csm in |- *; apply GraduationBetweenAnSn; immediate12.
	    since12 (Between A Cm Csm).
	     unfold Cm, Csm in |- *; apply GraduationBetweenAnSn; immediate12.
	     since12 (Between Bsm D Csm).
	      apply (ClockwiseSupplementAnglesBetween D Bsm Cm Csm).
	       since12 (Clockwise Bsm D Cm).
	       intro H21; contradict1 H19 H21.
	       from12 H18 (CongruentAngle Cm D Csm A B C).
	         step12 H21.
	         step12 H6.
	         from12 H15 (CongruentAngle Bsm D Cm Cm Bm Bsm).
	         step12 H22.
	      split.
	       step12 H21.
	         right; step12 H20.
	       split.
	        step12 H6.
	          as12 (CongruentAngle A Bm Cm Bm Bsm D).
	          step12 H12.
	        split.
	         step12 H18.
	           step12 H21.
	         step12 H8.
	           step12 H18.
	           as12 (Distance Bm Cm = Distance Bsm D).
	           usingChasles2 Bsm D Csm.
Qed.

Lemma  StrictParallelogrammExistM : forall A B C D E : Point,
	StrictParallelogramm A B C D ->
	Between B E C ->
	exists M : Point, Collinear A E M /\ Clockwise D C M.
Proof.
	intros.
	since12 (B <> E).
	destruct (ArchimedianDistanceLt B E C H1) as (n, (H2, H3)).
	from12 H0 (Clockwise A B E).
	since12 (A <> B).
	since12 (A <> E).
	generalize (DThales A B E H5 H6 H4 n H2).
	setGraduationPoint5 n A B ipattern:(Bn); fold Bn in |- *.
	setGraduationPoint5 n A E ipattern:(En); fold En in |- *.
	intros (H11, (H12, (H13, H14))).
	setStrictParallelogramm11 D A Bn ipattern:(F).
	 step12 H7.
	   immediate12.
	 DestructSP11 H16.
	   from12 H12 (CongruentAngle A Bn En A Bn F).
	  from12 H0 (CongruentAngle A B E A B C).
	    step12 H19.
	    as12 (Supplement A B C D A B).
	    from12 H7 (CongruentAngle D A B D A Bn).
	    step12 H21.
	    immediate12.
	  exists En; split.
	   immediate12.
	   from12 H19 (OpenRay Bn En F).
	     since12 (Clockwise A Bn F).
	     since12 (CongruentAngle A D C A D F).
	    as12 (CongruentAngle A D C A B C).
	      as12 (CongruentAngle A D F A Bn F).
	      from12 H0 (CongruentAngle A B C A B E).
	      step12 H24.
	      step12 H12.
	    since12 (CongruentAngle C D A F D A).
	      from12 H23 (OpenRay D C F).
	      step12 H24.
	     immediate12.
	     since12 (Between Bn F En).
	      apply DistanceLtBetween.
	       rewrite H14.
	         as12 (Distance Bn F = Distance A D).
	         as12 (Distance A D = Distance B C).
	       immediate12.
	       immediate12.
	      step12 H26.
	        left; immediate12.
Qed.

Lemma  StrictParallelogrammExistN : forall A B C D E : Point,
	StrictParallelogramm A B C D ->
	Between A E D ->
	exists N : Point, Collinear B E N /\ Clockwise D C N.
Proof.
	intros.
	since12 (A <> E).
	destruct (ArchimedianDistanceLt A E D H1) as (n, (H2, H3)).
	from12 H0 (Clockwise B E A).
	since12 (B <> E).
	since12 (B <> A).
	generalize (DThales B E A H5 H6 H4 n H2).
	setGraduationPoint5 n B A ipattern:(An); fold An in |- *.
	setGraduationPoint5 n B E ipattern:(En); fold En in |- *.
	intros (H11, (H12, (H13, H14))).
	setStrictParallelogramm11 An B C ipattern:(F).
	 step12 H7.
	   immediate12.
	 DestructSP11 H16.
	   from12 H13 (CongruentAngle En An B F An B).
	  from12 H0 (CongruentAngle B A E B A D).
	    step12 H19.
	    as12 (Supplement B A D C B A).
	    from12 H7 (CongruentAngle C B A C B An).
	    step12 H21.
	    immediate12.
	  exists En; split.
	   immediate12.
	   from12 H19 (OpenRay An En F).
	     since12 (CongruentAngle B C D B C F).
	    as12 (CongruentAngle B C D B A D).
	      as12 (CongruentAngle B C F B An F).
	      from12 H0 (CongruentAngle B A D B A E).
	      step12 H23.
	      step12 H13.
	    from12 H21 (OpenRay C D F).
	      step12 H22.
	     immediate12.
	     since12 (Between An F En).
	      apply DistanceLtBetween.
	       step12 H14.
	         as12 (Distance An F = Distance B C).
	         as12 (Distance A D = Distance B C).
	         as12 (DistanceTimes n A E = DistanceTimes n E A).
	       immediate12.
	       immediate12.
	      step12 H24.
	        right; immediate11.
Qed.

End DISCRETE_THALES.
