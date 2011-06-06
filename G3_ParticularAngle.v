Section PARTICULAR_ANGLES.

Ltac destructAngle A B C Hab Hac B' C' bac := 
unfold Angle at 1 in |- *; simpl in |- *;
unfold IntersectionCirclesPoint in |- *;
let H7 := fresh in let H8 := fresh in let H9 := fresh in let H10 := fresh in
(destruct (InterCirclesPointDef uCircle
    (Compass Uu  (InterDiameterPoint (Ruler A B Hab) (Compass A Oo Uu) (CollinearABA A B))
       (InterDiameterPoint (Ruler A C Hac) (Compass A Oo Uu) (CollinearABA A C)))) as (bac, ((H7, (H8, H9)), H10));
unfold InterDiameterPoint in *;
let H1 := fresh in let H2 := fresh in let H3 := fresh in
(destruct (InterDiameterPointDef (Ruler A B Hab) (Compass A Oo Uu)) as (B', ((H1, H2), H3));
let H4 := fresh in let H5 := fresh in let H6 := fresh in
(destruct (InterDiameterPointDef (Ruler A C Hac) (Compass A Oo Uu)) as (C', ((H4, H5), H6));
simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10))).

(* L'angle nul est represente par le point Uu. *)

Lemma InterPointLineOoUuuCircle : 
	Uu = InterDiameterPoint lineOoUu uCircle DiameterlineOoUuuCircle.
Proof.
	byDefEqPoint5; simpl in |- *; immediate5.
Qed.

Definition NullAngle ( A B C : Point)  := CongruentAngle A B C Uu Oo Uu.

Lemma NullAngleSym : forall A B C : Point,
	NullAngle A B C -> NullAngle C B A.
Proof.
	unfold NullAngle in |- *; intros.
	apply CongruentAngleRev1; immediate5.
Qed.

Lemma NullAngleDistinctBA : forall A B C : Point,
	NullAngle A B C ->
	B <> A.
Proof.
	unfold NullAngle in |- *; intros.
	apply (CongruentAngleDistinctBA A B C Uu Oo Uu H).
Qed.

Lemma NullAngleDistinctBC : forall A B C : Point,
	NullAngle A B C ->
	B <> C.
Proof.
	unfold NullAngle in |- *; intros.
	apply (CongruentAngleDistinctBC A B C Uu Oo Uu H).
Qed.

Lemma OpenRayNullAngle : forall A B C : Point,
	A <> B ->
	OpenRay A B C -> 
	NullAngle B A C.
Proof.
	unfold NullAngle in |- *; intros.
	from5 H0 (A <> C).
	 apply (CongruentEqAngle B A C Uu Oo Uu H H1 DistinctOoUu DistinctOoUu).
	   destructAngle A B C H H1 ipattern:D ipattern:E ipattern:alpha.
	   apply H5; intuition.
	  rewrite DistanceOoAngle; immediate5.
	  since5 (D = E).
	   apply H8; intuition.
	     step5 H10.
	   rewrite DistanceUuAngle.
	     rewrite H12; immediate5.
	  elim (NotClockwiseAngle Uu Oo Uu DistinctOoUu DistinctOoUu); immediate5.
Qed.

Lemma NullAngleOpenRay : forall A B C : Point,
	NullAngle B A C -> OpenRay A B C.
Proof.
	unfold NullAngle in |- *; intros.
	assert (Hab := CongruentAngleDistinctBA B A C Uu Oo Uu H).
	assert (Hac := CongruentAngleDistinctBC B A C Uu Oo Uu H).
	generalize  (EqCongruentAngle B A C Uu Oo Uu Hab Hac DistinctOoUu DistinctOoUu H).
	destructAngle A B C Hab Hac ipattern:D ipattern:E ipattern:alpha.
	intro; from5 H1 (D = E).
	   subst.
	   rewrite DistanceUuAngle.
	   immediate5.
	 step5 H8.
	   step5 H11.
	   step5 H5.
	   step5 H4.
Qed.

Lemma CongruentNullAngle : forall A B C D E F : Point,
	NullAngle A B C ->
	CongruentAngle A B C D E F ->
	NullAngle D E F.
Proof.
	unfold NullAngle in |- *; intros.
	apply (CongruentAngleTrans D E F A B C Uu Oo Uu).
	 apply CongruentAngleSym; exact H0.
	 exact H.
Qed.

Lemma NullCongruentAngle : forall A B C D E F : Point,
	NullAngle A B C ->
	NullAngle D E F ->
	CongruentAngle A B C D E F.
Proof.
	unfold NullAngle in |- *; intros.
	apply (CongruentAngleTrans A B C Uu Oo Uu).
	 immediate5.
	 apply CongruentAngleSym; immediate5.
Qed.

Lemma IsAngleNullAngle : IsAngle Uu.
Proof.
	unfold IsAngle in |- *; split; immediate5.
Qed.

Lemma EqNullAngle : forall (A B C : Point) (Hba : B <> A) (Hbc: B <> C) ,
	NullAngle A B C ->
	Angle A B C Hba Hbc = Uu.
Proof.
	intros.
	rewrite <- (EqAnglePoint Uu DistinctOoUu DistinctOoUu IsAngleNullAngle).
	apply EqCongruentAngle; exact H.
Qed.

Lemma NullEqAngle : forall (A B C : Point) (Hba : B <> A) (Hbc: B <> C),
	Angle A B C Hba Hbc = Uu->
	NullAngle A B C.
Proof.
	intros.
	apply (CongruentEqAngle A B C Uu Oo Uu Hba Hbc DistinctOoUu DistinctOoUu).
	rewrite (EqAnglePoint Uu DistinctOoUu DistinctOoUu IsAngleNullAngle); exact H.
Qed.

(* L'angle plat est represente par le point uU. *)

Definition uU := SymmetricPoint Uu Oo (sym_not_eq DistinctOoUu).

Definition ElongatedAngle ( A B C : Point)  := CongruentAngle A B C Uu Oo uU.

Lemma ElongatedAngleSym : forall A B C : Point,
	ElongatedAngle A B C -> ElongatedAngle C B A.
Proof.
	unfold ElongatedAngle in |- *; intros.
	apply CongruentAngleRev1; immediate5.
Qed.

Lemma ElongatedAngleDistinctBA : forall A B C : Point,
	ElongatedAngle A B C ->
	B <> A.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma ElongatedAngleDistinctBC : forall A B C : Point,
	ElongatedAngle A B C ->
	B <> C.
Proof.
	intros; inversion H; immediate5.
Qed.

Lemma SecondInterPointLineOoUuuCircle : 
	uU = SecondInterDiameterPoint lineOoUu uCircle DiameterlineOoUuuCircle.
Proof.
	step5 uU; simpl in |- *; immediate5.
Qed.

Lemma DistanceOouU : Distance Oo uU = Uu.
Proof.
	unfold uU in |- *; rewrite EqDistanceSymmetricPoint; immediate5.
Qed.

Lemma BetweenUuOouU : Between Uu Oo uU.
Proof.
	unfold uU in |- *; apply BetweenSymmetricPoint.
Qed.

Lemma DistinctOouU : Oo <> uU.
Proof.
	assert (H := BetweenUuOouU); immediate5.
Qed.

Lemma DistinctUuuU : Uu <> uU.
Proof.
	assert (H := BetweenUuOouU); immediate5.
Qed.

Lemma IsAngleElongatedAngle : IsAngle uU.
Proof.
	unfold IsAngle in |- *; split.
	 assert (H := DistanceOouU); immediate5.
	 assert (H := BetweenUuOouU); immediate5.
Qed.

Lemma BetweenElongatedAngle : forall A B C : Point,
	Between B A C -> ElongatedAngle B A C.
Proof.
	intros.
	assert (Hab : A <> B).
	 immediate5.
	 assert (Hac : A <> C).
	  immediate5.
	  apply (CongruentEqAngle B A C Uu Oo uU Hab Hac DistinctOoUu DistinctOouU).
	    destructAngle A B C Hab Hac ipattern:D ipattern:E ipattern:alpha.
	    rewrite (EqAnglePoint uU DistinctOoUu DistinctOouU).
	   unfold uU in |- *; byDefEqPoint5.
	     assert (Segment Uu alpha Oo).
	    apply ChaslesRec.
	      rewrite H0.
	      rewrite <- H7.
	      step5 H1.
	      step5 H4.
	      usingChasles2 D A E.
	      step5 H5.
	      step5 H8.
	      step5 H7.
	    step5 H10.
	      step5 H12.
	      step5 H0.
	   exact IsAngleElongatedAngle.
Qed.

Lemma ElongatedAngleBetween : forall A B C : Point,
	ElongatedAngle B A C -> Between B A C.
Proof.
	intros; inversion H.
	generalize H0; clear H0.
	destructAngle A B C Hba Hbc ipattern:D ipattern:E ipattern:alpha.
	rewrite (EqAnglePoint uU Hed Hef).
	 intro; step5 H5.
	   step5 H8.
	   subst; apply SegmentBetween.
	  apply ChaslesRec.
	    step5 H4.
	    step5 H0.
	    step5 H7.
	    step5 H1.
	    usingChasles2 Uu Oo uU.
	   immediate5.
	  step5 H4.
	  step5 H7.
	 exact IsAngleElongatedAngle.
Qed.

Lemma CongruentElongatedAngle : forall A B C D E F : Point,
	ElongatedAngle A B C ->
	CongruentAngle A B C D E F ->
	ElongatedAngle D E F.
Proof.
	unfold ElongatedAngle in |- *; intros.
	apply (CongruentAngleTrans D E F A B C Uu Oo uU).
	 apply CongruentAngleSym; exact H0.
	 exact H.
Qed.

Lemma ElongatedCongruentAngle : forall A B C D E F : Point,
	ElongatedAngle A B C ->
	ElongatedAngle D E F ->
	CongruentAngle A B C D E F.
Proof.
	unfold ElongatedAngle in |- *; intros.
	apply (CongruentAngleTrans A B C Uu Oo uU).
	 immediate5.
	 apply CongruentAngleSym; immediate5.
Qed.

Lemma EqElongatedAngle : forall (A B C : Point) (Hba : B <> A) (Hbc: B <> C) ,
	ElongatedAngle A B C ->
	Angle A B C Hba Hbc = uU.
Proof.
	intros.
	rewrite <- (EqAnglePoint uU DistinctOoUu DistinctOouU).
	 apply EqCongruentAngle.
	   exact H.
	 exact IsAngleElongatedAngle.
Qed.

Lemma ElongatedEqAngle : forall (A B C : Point) (Hba : B <> A) (Hbc: B <> C),
	Angle A B C Hba Hbc = uU->
	ElongatedAngle A B C.
Proof.
	intros.
	apply (CongruentEqAngle A B C Uu Oo uU Hba Hbc DistinctOoUu DistinctOouU).
	rewrite EqAnglePoint.
	 exact H.
	 exact IsAngleElongatedAngle.
Qed.

Lemma CongruentAngleCollinear : forall A B C D E F : Point,
	Collinear A B C ->
	CongruentAngle A B C D E F ->
	Collinear D E F.
Proof.
	intros.
	by3SegmentCases1 H.
	 since5 (OpenRay B C A).
	  since5 (NullAngle C B A).
	   apply OpenRayNullAngle.
	    apply (CongruentAngleDistinctBC _ _ _ _ _ _ H0).
	    immediate5.
	   since5 (NullAngle F E D).
	    apply NullAngleSym; apply (CongruentNullAngle A B C D E F).
	     apply NullAngleSym; immediate5.
	     immediate5.
	    since5 (OpenRay E F D).
	     apply NullAngleOpenRay; immediate5.
	 since5 (OpenRay B A C).
	  since5 (NullAngle A B C).
	   apply OpenRayNullAngle.
	    apply (CongruentAngleDistinctBA _ _ _ _ _ _ H0).
	    immediate5.
	   since5 (NullAngle D E F).	
	    apply (CongruentNullAngle A B C D E F); immediate5.
	    since5 (OpenRay E D F).
	     apply NullAngleOpenRay; immediate5.
	 since5 (ElongatedAngle A B C).
	  apply BetweenElongatedAngle; step5 H2.
	   apply sym_not_eq; apply (CongruentAngleDistinctBC _ _ _ _ _ _ H0).
	   apply (CongruentAngleDistinctBA _ _ _ _ _ _ H0).
	  since5 (ElongatedAngle D E F).
	   apply (CongruentElongatedAngle A B C D E F); immediate5.
	   since5 (Between D E F).
	    apply ElongatedAngleBetween; immediate5.
Qed.

Lemma NullAngleNotElongatedAngle : forall A B C : Point,
	NullAngle A B C -> ~ElongatedAngle A B C.
Proof.
	intros; intro.
	inversion H; inversion H0.
	elim DistinctUuuU.
	rewrite <- (EqNullAngle A B C Hba Hbc H).
	rewrite <- (EqElongatedAngle A B C Hba0 Hbc0 H0).
	apply EqCongruentAngle; apply CongruentAngleRefl; immediate5.
Qed.

Lemma ElongatedAngleNotNullAngle : forall A B C : Point,
 	ElongatedAngle A B C -> ~NullAngle A B C.
Proof.
	intros; intro.
	inversion H; inversion H0.
	elim DistinctUuuU.
	rewrite <- (EqNullAngle A B C Hba0 Hbc0 H0).
	rewrite <- (EqElongatedAngle A B C Hba Hbc H).
	apply EqCongruentAngle; apply CongruentAngleRefl; immediate5.
Qed.

End PARTICULAR_ANGLES.