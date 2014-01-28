Require Import A1_Plan A2_Orientation A5_Cercle A7_Tactics .
Require Import B7_Tactics .
Require Import C1_Distance C5_TriangularInequality C7_Tactics .
Require Import D1_IntersectionCirclesProp D5_Tactics .
Require Import F2_MarkSegment F5_Tactics .
Require Import G1_Angles G3_ParticularAngle G4_Tactics .
Require Import H1_Triangles H4_Tactics .
Require Import I1_SupplementaryAngle.

Section SUPPLEMENT.

Ltac destructAngle A B C Hba Hbc M := 
unfold Angle at 1 in |- *; simpl in |- *;
unfold IntersectionCirclesPoint in |- *;
let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in
(destruct (InterCirclesPointDef uCircle (Compass Uu (MarkSegmentPoint B A Oo Uu Hba) (MarkSegmentPoint B C Oo Uu Hbc))) as (M, ((H1, (H2, H3)), H4));
simpl in H1, H2, H3, H4).

Inductive  Supplement  (A B C D E F : Point)  : Prop := 
	| EqAngleSupplement : forall (Hba : B <> A) (Hbc : B <> C) (Hed : E <> D) (Hef : E <> F),
		Angle A B C Hba Hbc = Supplementary (Angle D E F Hed Hef)  (IsAngleAngle D E F Hed Hef) ->
		Supplement A B C D E F.

Lemma SupplementRev1 : forall A B C D E F : Point,
	Supplement A B C D E F ->
	Supplement C B A D E F.
Proof.
	intros.
	inversion H.
	apply (EqAngleSupplement C B A D E F Hbc Hba Hed Hef).
	rewrite <- H0.
	immediate7.
Qed.

Lemma SupplementSym : forall A B C D E F : Point,
	Supplement A B C D E F ->
	Supplement  D E F A B C.
Proof.
	intros.
	inversion H.
	apply (EqAngleSupplement D E F A B C Hed Hef Hba Hbc).
	apply  (SupplementarySym (Angle D E F Hed Hef) (Angle A B C Hba Hbc)  (IsAngleAngle D E F Hed Hef) (IsAngleAngle A B C Hba Hbc) H0).
Qed.

Lemma SupplementRev2 : forall A B C D E F : Point,
	Supplement A B C D E F ->
	Supplement A B C F E D.
Proof.
	intros.
	apply SupplementSym; apply SupplementRev1; apply SupplementSym; exact H.
Qed.

Lemma SupplementSupplementary : forall A B C D E F : Point, forall (Hba : B <> A) (Hbc : B <> C) (Hed : E <> D) (Hef : E <> F),
	Supplement A B C D E F ->
	Angle A B C Hba Hbc = Supplementary (Angle D E F Hed Hef) (IsAngleAngle D E F Hed Hef).
Proof.
	intros.
	inversion H.
	since7 (Angle A B C Hba Hbc = Angle A B C Hba0 Hbc0).
	 rewrite H1.
	   rewrite H0.
	   apply SupplementaryEqAngles.
	   immediate7.
Qed.

Lemma SupplementCongruentSupplement : forall A B C D E F K L M : Point, 
	Supplement A B C K L M ->
	CongruentAngle A B C D E F ->
	Supplement D E F K L M.
Proof.
	intros.
	inversion H.
	inversion H0.
	apply (EqAngleSupplement D E F K L M Hed0 Hef0 Hed Hef).
	rewrite <- H1; rewrite <- H2.
	immediate7.
Qed.

Lemma SupplementSupplementCongruent : forall A B C D E F K L M : Point, 
	Supplement A B C K L M ->
	Supplement D E F K L M ->
	CongruentAngle A B C D E F.
Proof.
	intros.
	inversion H.
	inversion H0.
	apply (CongruentEqAngle A B C D E F Hba Hbc Hba0 Hbc0).
	rewrite H1; rewrite H2.
	apply SupplementaryEqAngles; immediate7.
Qed.

Lemma BetweenSupplementAngles : forall A B C D : Point, 
	A <> C ->
	Between B A D ->
	Supplement B A C C A D.
Proof.
	intros A B C D Hac H.
	assert (Hab : A <> B).
	 immediate7.
	 assert (Had : A <> D).
	  immediate7.
	  setAngle6 B A C ipattern:alpha.
	    setAngle6 C A D ipattern:beta.
	    setMarkSegmentPoint5 A B Oo Uu ipattern:b; fold b in |- *.
	    setMarkSegmentPoint5 A C Oo Uu ipattern:c; fold c in |- *.
	    setMarkSegmentPoint5 A D Oo Uu ipattern:d; fold d in |- *.
	    since7 (Between b A d).
	   from7 H5 (OpenRay A D d).
	      step7 H4.
	    step7 H6.
	      from7 H1 (OpenRay A B b).
	       step7 H0.
	     step7 H7.
	   since7 (Distance b d = Distance Uu uU).
	    usingChasles2 b A d.
	      usingChasles2 Uu Oo uU.
	     step7 H0.
	     assert (Hb := BetweenUuOouU); immediate7.
	    byApartCases3 d b c.
	     immediate7.
	     since7 (TCongruent (Tr d A c) (Tr Uu Oo beta)).
	      step7 3.
	       step7 H2.
	         unfold beta in |- *; immediate7.
	       from7 H3 (CongruentAngle c A d C A D).
	          step7 H2.
	        step7 H10.
	          unfold beta in |- *; apply CongruentAngleUuOoAngle.
	      since7 (TCongruent (Tr b d c) (Tr uU Uu beta)).
	       step7 3.
	        step7 H10.
	        from7 H6 (CongruentAngle b d c A d c).
	         step7 H11.
	           from7 BetweenUuOouU (CongruentAngle uU Uu beta Oo Uu beta).
	            from7 H10 (Distance d c = Distance Uu beta).
	           step7 H12.
	          assert (H12 := BetweenUuOouU); immediate7.
	          step7 H12.
	            step7 H10.
	       apply (EqAngleSupplement B A C C A D Hab Hac Hac Had).
	         destructAngle B A C Hab Hac ipattern:gamma.
	         apply H15; repeat split.
	        unfold Supplementary in |- *; immediate7.
	        rewrite <- EqDistanceUuSupplementary.
	          fold beta b c in |- *; step7 H11.
	        unfold Supplementary in |- *; immediate7.
	     since7 (TCongruent (Tr b A c) (Tr Uu Oo alpha)).
	      step7 3.
	       step7 H2.
	         unfold alpha in |- *; immediate7.
	       from7 H3 (CongruentAngle b A c B A C).
	          step7 H2.
	        step7 H10.
	          unfold alpha in |- *; apply CongruentAngleUuOoAngle.
	      since7 (TCongruent (Tr d b c) (Tr uU Uu alpha)).
	       step7 3.
	        step7 H10.
	        from7 H6 (CongruentAngle d b c A b c).
	         step7 H11.
	           from7  BetweenUuOouU (CongruentAngle uU Uu alpha Oo Uu alpha).
	            from7 H10 (Distance b c = Distance Uu alpha).
	           step7 H12.
	          assert (H12 := BetweenUuOouU); immediate7.
	          step7 H12.
	            step7 H10.
	       apply SupplementSym.
	         apply (EqAngleSupplement C A D B A C Hac Had Hab Hac).
	         destructAngle C A D Hac Had ipattern:gamma.
	         apply H15; repeat split.
	        unfold Supplementary in |- *; immediate7.
	        rewrite <- EqDistanceUuSupplementary.
	          fold alpha c d in |- *; step7 H11.
	        unfold Supplementary in |- *; immediate7.
Qed.

Lemma ClockwiseSupplementAnglesBetween : forall A B C D : Point, 
	~Clockwise C A B -> 
	~Clockwise D A C -> 
	Supplement C A D  B A C ->
	Between B A D.
Proof.
	intros.
	inversion H1.
	setOppSegmentPoint5 A B A D ipattern:E.
	since7 (Supplement C A E B A C).
	 apply SupplementSym; apply BetweenSupplementAngles.
	  immediate7.
	  step7 H4.
	    step7 H3.
	 since7 (CongruentAngle C A D C A E).
	  apply (SupplementSupplementCongruent C A D C A E B A C); immediate7.
	  from7 H6 (D = E).
	     contrapose0 H.
	     step7 H4.
	   step7 H7.
	     step7 H4.
Qed.

Lemma AntiClockwiseSupplementAnglesBetween : forall A B C D : Point, 
	~Clockwise B A C -> 
	~Clockwise C A D -> 
	Supplement C A D B A C ->
	Between B A D.
Proof.
	intros.
	inversion H1.
	setOppSegmentPoint5 A B A D ipattern:E.
	since7 (Supplement C A E B A C).
	 apply SupplementSym; apply BetweenSupplementAngles.
	  immediate7.
	  step7 H4.
	    step7 H3.
	 since7 (CongruentAngle D A C E A C).
	  apply CongruentAngleRev;
	   apply (SupplementSupplementCongruent C A D C A E B A C); immediate7.
	  from7 H6 (D = E).
	     contrapose0 H.
	     step7 H4.
	   step7 H7.
	     step7 H4.
Qed.

Lemma SupplementUuuU : Supplement Uu Oo Uu Uu Oo uU.
Proof.
	apply BetweenSupplementAngles; immediate7.
Qed.

Lemma NullElongatedSupplement : forall A B C D E F : Point,
	NullAngle A B C ->
	ElongatedAngle D E F ->
	Supplement A B C D E F.
Proof.
	unfold NullAngle, ElongatedAngle in |- *; intros.
	apply (SupplementCongruentSupplement Uu Oo Uu).
	 apply SupplementSym; apply (SupplementCongruentSupplement Uu Oo uU).
	  apply SupplementSym; exact SupplementUuuU.
	  immediate7.
	 immediate7.
Qed.

Lemma NullSupplementElongated : forall A B C D E F : Point,
	NullAngle A B C ->
	Supplement A B C D E F ->
	ElongatedAngle D E F.
Proof.
	unfold NullAngle, ElongatedAngle in |- *; intros.
	apply (SupplementSupplementCongruent D E F Uu Oo uU A B C).
	 apply SupplementSym; exact H0.
	 apply SupplementSym; apply (SupplementCongruentSupplement Uu Oo Uu).
	  exact SupplementUuuU.
	  immediate7.
Qed.

Lemma ElongatedSupplementNull : forall A B C D E F : Point,
	ElongatedAngle D E F ->
	Supplement A B C D E F ->
	NullAngle A B C.
Proof.
	unfold NullAngle, ElongatedAngle in |- *; intros.
	apply (SupplementSupplementCongruent A B C Uu Oo Uu D E F).
	 immediate7.
	 apply SupplementSym; apply (SupplementCongruentSupplement Uu Oo uU).
	  apply SupplementSym; exact SupplementUuuU.
	  immediate7.
Qed.

Lemma TriangleBetween : forall A B C I J K L M : Point,
	Clockwise I J K  ->
	Clockwise I K L  ->
	Clockwise I L M  ->
	CongruentAngle C A B J I K ->
	CongruentAngle A B C K I L  ->
	CongruentAngle B C A L I M  ->
	Between J I M.
Proof.
	intros.
	setMarkSegmentPoint5 I K A B ipattern:K'.
	setMarkSegmentPoint5 I L B C ipattern:L'.
	from7 2 (TCongruent (Tr I K' L') (Tr B A C)).
	   from7 H7 (CongruentAngle L' I K' L I K).
	   step7 H9; immediate7.
	   step7 H6; immediate7.
	  step7 H11; immediate7.
	  apply (SumAngles I J K' L' M).
	   step7 H7.
	     step7 H6; immediate7.
	   step7 H7.
	    step7 H6; immediate7.
	    step7 H10.
	      step7 H9; immediate7.
	   step7 H10.
	     step7 H9; immediate7.
	   step7 H11.
	    step7 H6; immediate7.
	    since7 (Distance K' L' = Distance A C).
	     step7 H12; immediate7.
	    step7 H2.
	      step7 H7.
	   step7 H11.
	    since7 (Distance K' L' = Distance A C).
	     step7 H12; immediate7.
	    step7 H9; immediate7.
	    step7 H4.
	      step7 H10.
Qed.

Lemma TriangleSupplement : forall A B C I J K L M : Point,
	Clockwise I J K  ->
	Clockwise I K L  ->
	Clockwise I L M  ->
	CongruentAngle C A B J I K ->
	CongruentAngle A B C K I L  ->
	CongruentAngle B C A L I M  ->
	Supplement J I L L I M.
Proof.
	intros.
	apply BetweenSupplementAngles.
	 immediate7.
	 apply (TriangleBetween A B C I J K L M); immediate7.
Qed.

Lemma TriangleSumSupplement : forall A B C I J K L : Point,
	Clockwise I J K  ->
	Clockwise I K L  ->
	CongruentAngle C A B J I K ->
	CongruentAngle A B C K I L  ->
	Supplement J I L B C A.
Proof.
	intros.
	since7 (~ Collinear A B C).
	 intro.
	   by2Cases1 H3.
	  since7 (OpenRay I K J).
	   apply NullAngleOpenRay.
	     step7 H1.
	     step7 H4.
	     step7 H4.
	     immediate7.
	   contradict1 H H5.
	  since7 (OpenRay I K L).
	   apply NullAngleOpenRay.
	     step7 H2.
	   contradict1 H0 H5.
	 setMarkSegmentPoint5 I L B C ipattern:L'.
	   setTCongruentClockwise7 B C A L' I ipattern:M.
	   from7 H10 (CongruentAngle B C A L I M).	
	    step7 H6.
	  apply SupplementSym;
	   apply (SupplementCongruentSupplement L I M B C A J I L).
	   apply SupplementSym; apply (TriangleSupplement A B C I J K L M);  try immediate7.
	     step7 H11.
	   immediate7.
Qed.

Lemma TriangleSumClockwise : forall A B C I J K L M : Point,
	Clockwise I J K  ->
	Clockwise I K L  ->
	CongruentAngle C A B J I K ->
	CongruentAngle A B C K I L  ->
	Between J I M ->
	Clockwise I L M.
Proof.
	intros.
	setMarkSegmentPoint5 I L B C ipattern:L'.
	setTCongruentClockwise7 B C A L' I ipattern:M'.
	 intro; from7 H1 (Collinear J I K).
	  contradict1 H H8.
	 since7 (Between J I M').
	  apply (TriangleBetween A B C I J K L M').
	   immediate7.
	   immediate7.
	   step7 H6.
	   immediate7.
	   immediate7.
	   step7 H10.
	     step7 H6.
	  step7 H3.
	    right; step7 H6.
	    step7 H12.
Qed.

End SUPPLEMENT.

