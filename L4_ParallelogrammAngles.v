
Section PARALLELOGRAMM_ANGLES.

Lemma ParallelogrammDABeqBCD : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> B -> 
	B <> C -> 
	CongruentAngle D A B B C D.
Proof.
	intros.
	assert (H4 := ParallelogrammTCongruentBCDDAB A B C D H).
	step10 H4.
	 apply (ParallelogrammDistinctABDistinctCD A B C D H H0).
	 apply sym_not_eq; apply (ParallelogrammDistinctBCDistinctDA A B C D H H1).
Qed.

Lemma StrictParallelogrammDABeqBCD : forall A B C D : Point,
	StrictParallelogramm A B C D ->
	CongruentAngle D A B B C D.
Proof.
	intros; apply ParallelogrammDABeqBCD.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma ParallelogrammABCeqCDA : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> B -> 
	B <> C -> 
	CongruentAngle A B C C D A.
Proof.
	intros.
	assert (H4 := ParallelogrammTCongruentABCCDA A B C D H).
	step10 H4.
	 apply sym_not_eq; apply (ParallelogrammDistinctABDistinctCD A B C D H H0).
	 apply (ParallelogrammDistinctBCDistinctDA A B C D H H1).
Qed.

Lemma StrictParallelogrammABCeqCDA : forall A B C D : Point,
	StrictParallelogramm A B C D ->
	CongruentAngle A B C C D A.
Proof.
	intros; apply ParallelogrammABCeqCDA.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma ParallelogrammBACeqDCA : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> B -> 
	CongruentAngle B A C D C A.
Proof.
	intros; inversion H.
	assert (H3 := ParallelogrammTCongruentABCCDA A B C D H).
	step10 H3.
	apply (ParallelogrammDistinctABDistinctCD A B C D H H0).
Qed.

Lemma StrictParallelogrammBACeqDCA : forall A B C D : Point,
	StrictParallelogramm A B C D ->
	CongruentAngle B A C D C A.
Proof.
	intros; apply ParallelogrammBACeqDCA.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
Qed.

Lemma ParallelogrammDACeqBCA : forall A B C D : Point,
	Parallelogramm A B C D ->
	B <> C -> 
	CongruentAngle D A C B C A.
Proof.
	intros; inversion H.
	assert (H3 := ParallelogrammTCongruentABCCDA A B C D H).
	step10 H3.
	apply sym_not_eq; apply (ParallelogrammDistinctBCDistinctDA A B C D H H0).
Qed.

Lemma StrictParallelogrammDACeqBCA : forall A B C D : Point,
	StrictParallelogramm A B C D ->
	CongruentAngle D A C B C A.
Proof.
	intros; apply ParallelogrammDACeqBCA.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma ParallelogrammABDeqCDB : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> B -> 
	CongruentAngle A B D C D B.
Proof.
	intros; inversion H.
	assert (H3 := ParallelogrammTCongruentBCDDAB A B C D H).
	step10 H3.
	apply sym_not_eq; apply (ParallelogrammDistinctABDistinctCD A B C D H H0).
Qed.

Lemma StrictParallelogrammABDeqCDB : forall A B C D : Point,
	StrictParallelogramm A B C D ->
	CongruentAngle A B D C D B.
Proof.
	intros; apply ParallelogrammABDeqCDB.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
Qed.

Lemma ParallelogrammADBeqCBD : forall A B C D : Point,
	Parallelogramm A B C D ->
	B <> C -> 
	CongruentAngle A D B C B D.
Proof.
	intros; inversion H.
	assert (H3 := ParallelogrammTCongruentBCDDAB A B C D H).
	step10 H3.
	apply (ParallelogrammDistinctBCDistinctDA A B C D H H0).
Qed.

Lemma StrictParallelogrammADBeqCBD : forall A B C D : Point,
	StrictParallelogramm A B C D ->
	CongruentAngle A D B C B D.
Proof.
	intros; apply ParallelogrammADBeqCBD.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma StrictParallelogrammExteriorAngles : forall A B C D E : Point, 
	StrictParallelogramm A B C D ->
	Between A B E ->
	CongruentAngle D A B C B E.
Proof.
	intros.
	since10 (Clockwise C D B).
	 step10 (StrictParallelogrammClockwiseBCD A B C D H).
	 pose (G := StrictPVertex4 C D B H1).
	   pose (H2 := StrictPVertex4Parallelogramm C D B H1); fold G in H2.
	   since10 (Between G B A).
	  apply (SumAngles B G C D A).
	   step10 (StrictParallelogrammClockwiseCDA C D B G H2).
	   immediate10.
	   step10 (StrictParallelogrammClockwiseDAB A B C D H).
	   step10 (StrictParallelogrammBACeqDCA C D B G H2).
	   step10 (StrictParallelogrammABDeqCDB A B C D H).
	  since10 (OpenRay B E G).
	   canonize1.
	     step10 H6.
	     step10 H5.
	   since10 (CongruentAngle C B E C B G).
	    step10 H5.
	      step10 (StrictParallelogrammDABeqBCD A B C D H).
	      step10 (StrictParallelogrammBACeqDCA C D B G H2).
Qed.

Lemma StrictParallelogrammAlternateAngles : forall A B C D E : Point, 
	StrictParallelogramm A B C D ->
	Between C B E ->
	CongruentAngle D A B E B A.
Proof.
	intros.
	setSymmetricPoint5 A B ipattern:G.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 since10 (OpposedAngles B E A C G).
	  since10 (CongruentAngle E B A C B G).
	   step10 H5.
	     apply CongruentAngleSym; apply (StrictParallelogrammExteriorAngles A B C D G H).
	    immediate10.
Qed.

Lemma ParallelogrammSegmentElongated : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> D ->
	Segment A B C ->
	ElongatedAngle D A B.
Proof.
	intros.
	since10 (Segment D C A).
	 usingChaslesRec2.
	   rewrite <- (ParallelogrammBCeqDA A B C D H).
	   rewrite (DistanceSym D C).
	   rewrite <- (ParallelogrammABeqCD A B C D H).
	   usingChasles2 A C B.
	 from10 H2 (Between D A B).
	    step10 H2.
	    inversion H; immediate10.
Qed.

Lemma BetweenBetweenElongated : forall A B C E : Point, 
	Between A B E ->
	Between A C B ->
	ElongatedAngle C B E.
Proof.
	intros.
	from10 H (Between C B E).
Qed.

Lemma ParallelogrammSegmentElongated2 : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> B ->
	Segment B C A ->
	ElongatedAngle D A B.
Proof.
	intros.
	from10 H1 (Between D A B).
	  since10 (Segment A D C).
	   usingChaslesRec2.
	     rewrite (DistanceSym A D).
	     rewrite <- (ParallelogrammBCeqDA A B C D H).
	     rewrite <- (ParallelogrammABeqCD A B C D H).
	     usingChasles2 B A C.
	  step10 H1.
	    inversion H; immediate10.
Qed.

Lemma BetweenBetweenElongated2 : forall A B C E : Point, 
	Between A B E ->
	Between C A B ->
	ElongatedAngle C B E.
Proof.
	intros.
	from10 H (Between C B E).
Qed.

Lemma ParallelogrammSegmentNull3 : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> B ->
	A <> D ->
	Segment C A B ->
	NullAngle D A B.
Proof.
	intros.
	since10 (OpenRay A B D).
	 since10 (OpenRay A B C).
	  step10 H3.
	    since10 (Segment A C D).
	   usingChaslesRec2.
	     rewrite (DistanceSym A D).
	     rewrite <- (ParallelogrammBCeqDA A B C D H).
	     rewrite (DistanceSym D C).
	     rewrite <- (ParallelogrammABeqCD A B C D H).
	     usingChasles2 A B C.
Qed.

Lemma BetweenBetweenNull3 : forall A B C E : Point, 
	Between A B E ->
	Between C B A ->
	NullAngle C B E.
Proof.
	intros.
	since10 (OpenRay B C E).
	 canonize1.
	   step10 H2.
	   step10 H3.
Qed.

Lemma ParallelogrammColinearExteriorAngles : forall A B C D E : Point, 
	Parallelogramm A B C D ->
	A <> D ->
	Between A B E ->
	Collinear A B C ->
	CongruentAngle D A B C B E.
Proof.
	intros.
	by3SegmentCases1 H2.
	 since10 (ElongatedAngle C B E).
	  apply (BetweenBetweenElongated A).
	   immediate10.
	   step10 H3.
	    inversion H; immediate10.
	    assert (H4 := ParallelogrammDistinctDADistinctBC A B C D H).
	      apply sym_not_eq; apply H4; immediate10.
	  step10 H4.
	    apply (ParallelogrammSegmentElongated A B C D); immediate10.
	 since10 (ElongatedAngle C B E).
	  apply (BetweenBetweenElongated2 A).
	   immediate10.
	   step10 H4.
	     inversion H; immediate10.
	  step10 H3.
	    apply (ParallelogrammSegmentElongated2 A B C D); immediate10.
	 since10 (NullAngle C B E).
	  apply (BetweenBetweenNull3 A).
	   immediate10.
	   step10 H4.
	     apply sym_not_eq; apply (ParallelogrammDistinctDADistinctBC A B C D H).
	     immediate10.
	  step10 H3.
	    apply (ParallelogrammSegmentNull3 A B C D); immediate10.
Qed.

Lemma ParallelogrammExteriorAngles : forall A B C D E : Point, 
	Parallelogramm A B C D ->
	A <> D ->
	Between A B E ->
	CongruentAngle D A B C B E.
Proof.
	intros.
	by3Cases1 A B C.
	 pose (H3 := SPDef H H2).
	   apply (StrictParallelogrammExteriorAngles A B C D E H3).
	   immediate10.
	 since10 (Parallelogramm C B A D).
	  do 2 apply ParallelogrammPerm; apply ParallelogrammRev; immediate10.
	  since10 (Clockwise C B A).
	   pose (H5 := SPDef H2 H4).
	     since10 (CongruentAngle D C B E B C).
	    apply (StrictParallelogrammAlternateAngles C B A D E H5); immediate10.
	    step10 H6.
	      since10 (CongruentAngle D A B B C D).
	     apply (ParallelogrammDABeqBCD A B C D H); immediate10.
	 apply ParallelogrammColinearExteriorAngles; immediate10.
Qed.

Lemma ParallelogrammAlternateAngles : forall A B C D E : Point, 
	Parallelogramm A B C D ->
	A <> B ->
	Between C B E ->
	CongruentAngle D A B E B A.
Proof.
	intros.
	since10 (CongruentAngle D A B B C D).
	 apply ParallelogrammDABeqBCD; immediate10.
	 step10 H2.
	   since10 (CongruentAngle D C B A B E).
	  apply ParallelogrammExteriorAngles.
	   apply ParallelogrammRev.
	     do 2 apply ParallelogrammPerm; immediate10.
	   apply (ParallelogrammDistinctABDistinctCD A B C D H H0).
	   immediate10.
Qed.

Lemma ParallelogrammDABSupplementAngleABC : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> B  ->
	B <> C  ->
	Supplement D A B A B C.
Proof.
	intros.
	setSymmetricPoint5 A B ipattern:G.
	since10 (CongruentAngle D A B C B G).
	 assert (H4 := sym_not_eq (ParallelogrammDistinctBCDistinctDA A B C D H H1)).
	   apply (ParallelogrammExteriorAngles A B C D G H H4 H3).
	 step10 H4.
Qed.

Lemma StrictParallelogrammDABSupplementAngleABC : forall A B C D : Point, 
	StrictParallelogramm A B C D ->
	Supplement D A B A B C.
Proof.
	intros; apply ParallelogrammDABSupplementAngleABC.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma ParallelogrammABCSupplementAngleBCD : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> B ->
	B <> C  ->
	Supplement A B C B C D.
Proof.
	intros.
	assert (H2 := ParallelogrammDABSupplementAngleABC A B C D H H0 H1).
	step10 H2.
	apply ParallelogrammDABeqBCD; immediate10.
Qed.

Lemma StrictParallelogrammABCSupplementAngleBCD : forall A B C D : Point, 
	StrictParallelogramm A B C D ->
	Supplement A B C B C D.
Proof.
	intros; apply ParallelogrammABCSupplementAngleBCD.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma ParallelogrammBCDSupplementAngleCDA : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> B  ->
	B <> C  ->
	Supplement B C D C D A.
Proof.
	intros.
	assert (H2 := ParallelogrammABCSupplementAngleBCD A B C D H H0 H1).
	step10 H2.
	apply ParallelogrammABCeqCDA; immediate10.
Qed.

Lemma StrictParallelogrammBCDSupplementAngleCDA : forall A B C D : Point, 
	StrictParallelogramm A B C D ->
	Supplement B C D C D A.
Proof.
	intros; apply ParallelogrammBCDSupplementAngleCDA.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma ParallelogrammCDASupplementAngleDAB : forall A B C D : Point, 
	Parallelogramm A B C D ->
	A <> B  ->
	B <> C  ->
	Supplement C D A D A B.
Proof.
	intros.
	assert (H2 := ParallelogrammBCDSupplementAngleCDA A B C D H H0 H1).
	step10 H2.
	apply CongruentAngleSym; apply ParallelogrammDABeqBCD; immediate10.
Qed.

Lemma StrictParallelogrammCDASupplementAngleDAB : forall A B C D : Point, 
	StrictParallelogramm A B C D ->
	Supplement C D A D A B.
Proof.
	intros; apply ParallelogrammCDASupplementAngleDAB.
	 destruct H; immediate10.
	 apply (StrictParallelogrammDistinctAB A B C D H).
	 apply (StrictParallelogrammDistinctBC A B C D H).
Qed.

Lemma CongruentAnglesParallelogramm : forall A B C D : Point, 
	Clockwise A B C ->
	Clockwise C B D ->
	CongruentAngle A B C B C D ->
	Distance A B = Distance C D ->
	StrictParallelogramm A B D C.
Proof.
	intros.
	since10 (TCongruent (Tr A B C) (Tr D C B)).
	since10 (StrictParallelogramm C A B D).
	 apply EquiDistantStrictParallelogramm; immediate10.
	 apply StrictParallelogrammPerm; immediate10.
Qed.

Lemma SupplementParallelogramm : forall A B C D : Point, 
	Clockwise A B C ->
	Clockwise B C D ->
	Supplement A B C B C D ->
	Distance A B = Distance C D ->
	StrictParallelogramm A B C D.
Proof.
	intros.
	setSymmetricPoint5 D C ipattern:E.
	since10 (StrictParallelogramm A B E C).
	 apply CongruentAnglesParallelogramm.
	  immediate10.
	  step10 H5.
	  step10 H1.
	  immediate10.
	 since10 (TCongruent (Tr B E C) (Tr A C D)).
	  step10 3.
	   destruct H6 as (Hp, H7).
	     assert (H8 := ParallelogrammBCeqDA A B E C Hp); immediate10.
	   apply ParallelogrammExteriorAngles.
	    inversion H6.
	      do 2 apply ParallelogrammPerm; immediate10.
	    apply sym_not_eq; apply (StrictParallelogrammDistinctBC A B E C H6).
	    immediate10.
	  apply EquiDistantStrictParallelogramm.
	   immediate10.
	   step10 H5.
	     left; apply (StrictParallelogrammClockwiseCDA A B E C H6).
	   immediate10.
	   immediate10.
Qed.

End PARALLELOGRAMM_ANGLES.
