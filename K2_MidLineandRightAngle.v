Section MIDLINEandRIGHTANGLE.

Lemma RightAngleNotCollinear : forall A B C : Point,
	RightAngle A B C ->
	~Collinear A B C.
Proof.
	intros; intro.
	by3SegmentCases1 H0.
	 elim (RightAngleNotNullAngle A B C H).
	   apply OpenRayNullAngle.
	  apply (RightAngleDistinctBA A B C H).
	  step9 H1.
	    apply (RightAngleDistinctBC A B C H).
	 elim (RightAngleNotNullAngle A B C H).
	   apply OpenRayNullAngle.
	  apply (RightAngleDistinctBA A B C H).
	  immediate9.
	 elim (RightAngleNotElongatedAngle A B C H).
	   apply BetweenElongatedAngle.
	   step9 H2.
	  apply sym_not_eq; apply (RightAngleDistinctBC A B C H).
	  apply (RightAngleDistinctBA A B C H).
Qed.

Lemma SupplementaryRightAngle : Supplementary Vv IsAngleVv = Vv.
Proof.
	unfold Supplementary in |- *.
	assert (H := IsAngleVv); eqToCongruent8.
	exact RightVvOouU.
Qed.

Lemma EqSupplementaryEqRightAngle : forall alpha : Point, forall (H : IsAngle alpha),
	Supplementary alpha H = alpha ->
	alpha = Vv.
Proof.
	unfold Supplementary, RightAngle in |- *; intros.
	from9 3 (TCongruent (Tr alpha Oo uU) (Tr alpha Oo Uu)).
	   eqToCongruent8; immediate9.
	 apply EqVv.
	  immediate9.
	  elim H; intros.
	    contrapose0 H3.
	    step9 BetweenUuOouU.
	  step9 H1.
Qed.

Lemma EqSupplementEqRightAngle : forall A B C : Point,
	Supplement A B C A B C ->
	RightAngle A B C.
Proof.
	intros.
	inversion H.
	since9 (Angle A B C Hed Hef = Vv).
	 apply  (EqSupplementaryEqRightAngle (Angle A B C Hed Hef) (IsAngleAngle A B C Hed Hef)).
	  step9 H0.
	 unfold RightAngle in |- *.
	   congruentToEq8.
	  exact DistinctOoVv.
	  rewrite H1.
	    assert (H4 := IsAngleVv).
	    step9 H4.
Qed.

Lemma SupplementCongruentRightAngle : forall A B C D E F : Point,
	CongruentAngle A B C D E F ->
	Supplement A B C D E F ->
	RightAngle A B C.
Proof.
	intros.
	apply EqSupplementEqRightAngle.
	step9 H0.
Qed.

Lemma RightAngleAIA' : forall A B : Point, forall H : A <> B, 
	RightAngle A (MidPoint A B H) (LineA (MidLine A B H)).
Proof.
	intros.
	apply EqSupplementEqRightAngle.
	since9  (CongruentAngle A (MidPoint A B H) (LineA (MidLine A B H)) B (MidPoint A B H) (LineA (MidLine A B H))).
	 assert (H1 := TCongruentAIA'BIA' A B H).
	   step9 H1;  immediate9.
	 step9 H0.
	   since9 (Between A (MidPoint A B H) B).
Qed.

Lemma RightAngleAIB' : forall A B : Point, forall H : A <> B, 
	RightAngle A (MidPoint A B H) (LineB (MidLine A B H)).
Proof.
	intros.
	apply (CongruentRightAngle A (MidPoint A B H) (LineA (MidLine A B H))).
	 apply RightAngleAIA'.
	 step9 (TCongruentAIA'AIB' A B H);  immediate9.
Qed.

Lemma RightAngleBIA' : forall A B : Point, forall H : A <> B, 
	RightAngle B (MidPoint A B H) (LineA (MidLine A B H)).
Proof.
	intros.
	apply (CongruentRightAngle A (MidPoint A B H) (LineA (MidLine A B H))).
	 apply RightAngleAIA'.
	 step9 (TCongruentAIA'BIA' A B H);  immediate9.
Qed.

Lemma RightAngleBIB' : forall A B : Point, forall H : A <> B, 
	RightAngle B (MidPoint A B H) (LineB (MidLine A B H)).
Proof.
	intros.
	apply (CongruentRightAngle A (MidPoint A B H) (LineB (MidLine A B H))).
	 apply RightAngleAIB'.
	 step9 (TCongruentAIB'BIB' A B H);  immediate9.
Qed.

Lemma OnMidLineRightAngle : forall A B C : Point, forall H : A <> B, 
	MidPoint A B H <> C ->
	OnLine (MidLine A B H) C ->
	RightAngle A (MidPoint A B H) C.
Proof.
	intros.
	from9 1 (TCongruent (Tr A (MidPoint A B H) C) (Tr B (MidPoint A B H) C)).
	  step9 H1.
	 from9 H2 (CongruentAngle A (MidPoint A B H) C B (MidPoint A B H) C).
	  apply EqSupplementEqRightAngle.
	    step9 H3.
	    since9 (Between A (MidPoint A B H) B).
Qed.

Lemma OnMidLineEqMidPointRightAngleA : forall A B C D : Point, forall H : A <> B, 
	C <> D ->
	C = MidPoint A B H ->
	OnLine (MidLine A B H) D ->
	RightAngle A  C D.
Proof.
	intros.
	subst.
	apply OnMidLineRightAngle; immediate9.
Qed.

Lemma OnMidLineEqMidPointRightAngleB : forall A B C D : Point, forall H : A <> B, 
	C <> D ->
	C = MidPoint A B H ->
	OnLine (MidLine A B H) D ->
	RightAngle B  C D.
Proof.
	intros; subst.
	apply (CongruentRightAngle A (MidPoint A B H) D).
	 apply (OnMidLineEqMidPointRightAngleA A B (MidPoint A B H) D H); immediate9.
	 from9 1 (TCongruent (Tr A (MidPoint A B H) D) (Tr B (MidPoint A B H) D)).
	   step9 H2.
	  step9 H1.
	   immediate9.
	   immediate9.
Qed.

Lemma RightSupplementUuOoVv :
	Supplement Uu Oo Vv Uu Oo Vv.
Proof.
	assert (H := IsAngleVv).
	congruentToEq8.
	 immediate9.
	 since9  (Supplementary (Angle Uu Oo Vv H0 H1) (IsAngleAngle Uu Oo Vv H0 H1) = Supplementary Vv IsAngleVv).
	  rewrite H2; rewrite SupplementaryRightAngle.
	    immediate9.
Qed.

Lemma RightRightSupplement : forall A B C D E F : Point,
	RightAngle A B C ->
	RightAngle D E F ->
	Supplement A B C D E F.
Proof.
	unfold RightAngle in |- *; intros.
	step9 H.
	apply SupplementSym; step9 H0.
	exact RightSupplementUuOoVv.
Qed.

Lemma RightSupplement : forall A B C : Point,
	RightAngle A B C ->
	Supplement A B C A B C.
Proof.
	intros; apply RightRightSupplement; immediate9.
Qed.

Lemma RightSupplementRight : forall A B C D E F : Point,
	RightAngle A B C ->
	Supplement A B C D E F ->
	RightAngle D E F.
Proof.
	intros; apply (CongruentRightAngle A B C D E F H).
	apply CongruentAngleSym; step9 H0.
	apply RightSupplement; immediate9.
Qed.

Lemma OrSupplementRight : forall A B C D E F : Point,
	RightAngle A B C \/ CongruentAngle A B C D E F ->
	Supplement A B C D E F ->
	RightAngle D E F.
Proof.
	intros; destruct H.
	 apply (RightSupplementRight A B C D E F H H0).
	 apply (SupplementCongruentRightAngle D E F A B C).
	  immediate9.
	  apply SupplementSym; immediate9.
Qed.

Lemma RightOrRight : forall A B C D E F : Point,
	RightAngle A B C ->
	Supplement A B C D E F \/ CongruentAngle A B C D E F ->
	RightAngle D E F.
Proof.
	intros.
	destruct H0.
	 apply (RightSupplementRight A B C D E F H H0).
	 apply (CongruentRightAngle A B C D E F H H0).
Qed.

End MIDLINEandRIGHTANGLE.
