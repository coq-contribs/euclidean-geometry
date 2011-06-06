Section SECOND_DIMENSION.

Ltac setClockwise A B H C :=
	pose (C := ExistsClockwise A B H);
	let Hyp := fresh in (
	assert (Hyp := ClockwiseExistsClockwise A B H);
	fold C in Hyp).

Lemma OpenRayDistinct : forall A B C : Point,
	A <> B -> OpenRay A B C -> A <> C.
Proof.
	intros.
	setClockwise A B H ipattern:D.
	from2 H0 (Clockwise A D C).
Qed.

Lemma BetweenDistinctBC : forall A B C : Point,
	Between A B C -> B <> C.
Proof.
	intros A B C (H, H0).
	setClockwise A B H ipattern:D.
	from2 H0 (Clockwise B D C).
Qed.

Lemma BetweenSym : forall A B C : Point,
	Between A B C -> Between C B A.
Proof.
	intros A B C (H, H0); split.
	 apply sym_not_eq; apply (BetweenDistinctBC A B C); canonize1.
	 immediate2.
Qed.

Lemma  BetweenDistinctAC : forall A B C : Point,
	Between A B C -> A <> C.
Proof.
	intros A B C (H, H0).
	apply (OpenRayDistinct A B C H).
	apply BetweenOpenRayAB; canonize1.
Qed.

Lemma BetweenOpenRayCA : forall A B C : Point,
	Between A B C -> OpenRay C A B.
Proof.
	intros; apply OpenRaySym.
	 apply sym_not_eq; apply (BetweenDistinctBC _ _ _ H).
	 apply BetweenOpenRayCB; trivial.
Qed.

Lemma BetweenTransACD : forall A B C D : Point,
	Between A B C ->
	Between B C D ->
	Between A C D.
Proof.
	intros.
	apply BetweenSym; apply (OpenRayBetween D C B A).
	 immediate2.
	 apply BetweenSym; immediate2.
Qed.

Lemma BetweenTransBCD : forall A B C D : Point,
	Between A B C ->
	Between A C D ->
	Between B C D.
Proof.
	intros.
	apply BetweenSym; apply (OpenRayBetween D C A B).
	 apply BetweenOpenRayCA; immediate2.
	 apply BetweenSym; immediate2.
Qed.

Lemma BetweenTransABD : forall A B C D : Point,
	Between A B C ->
	Between A C D ->
	Between A B D.
Proof.
	intros; split.
	 immediate2.
	 assert (H1 := BetweenTransBCD A B C D H H0).
	   assert (H2 := BetweenOpenRayAC B C D H1).
	   step2 H2.
	   apply (BetweenDistinctAC B C D H1).
Qed.

Lemma Apart : forall A B C : Point,
	A <> B -> A <> C \/ B <> C.
Proof.
	intros.
	by4Cases1 A B C.
	 right; immediate2.
	 right; immediate2.
	 left; apply (OpenRayDistinct A B C H H0).
	 right; apply (OpenRayDistinct B A C); auto.
Qed.

Lemma EquiOrientedDistinct : forall A B C D : Point,
	A <> B -> EquiOriented A B C D ->
	C <> D.
Proof.
	intros.
	setClockwise B A (sym_not_eq H) ipattern:E.
	from2 H0 (Clockwise C D E).
Qed.

Lemma BetweenClockwiseOrClockwiseBC : forall A B C M : Point,
	Between A B C -> Clockwise A B M \/ Clockwise A C M ->
	Clockwise B C M.
Proof.
	intros.
	assert (H1 := BetweenOpenRayAB A B C H).
	canonize1.
	apply H3; step2 H1; trivial.
Qed.

Lemma BetweenClockwiseOrClockwiseAC : forall A B C M : Point,
	Between A B C -> Clockwise A B M \/ Clockwise B C M ->
	Clockwise A C M.
Proof.
	intros.
	assert (H1 := BetweenOpenRayAB A B C H).
	canonize1.
	apply H1; step2 H3.
Qed.

Lemma BetweenClockwiseOrClockwiseAB : forall A B C M : Point,
	Between A B C -> Clockwise A C M \/ Clockwise B C M ->
	Clockwise A B M.
Proof.
	intros.
	assert (H1 := BetweenOpenRayAB A B C H).
	canonize1.
	 step2 H1; trivial.
	 step2 H3; trivial.
Qed.

Lemma OpenRaysBetween : forall A B C D E : Point,
	Between B A C -> 
	OpenRay A B D  ->
	OpenRay A C E ->
	Between D A E.
Proof.
	canonize1.
	 subst.
	   setClockwise B A H2 ipattern:F.
	   elim (NotClockwiseAAB A F); step2 H.
	 step2 H1.
	   step2 H3.
	   step2 H0.
Qed.

Lemma DistinctOrDistinct : forall A B C D : Point,
	A <> B ->
	(Distance A B = Distance C D) \/
	(EquiOriented A B C D) ->
	C <> D.
Proof.
	intros A B C D H [H0| H1].
	 apply (DistinctEqDistanceDistinct A B C D H H0).
	 apply (EquiOrientedDistinct A B C D H H1).
Qed.

Lemma DistinctOrDistinctABC : forall A B C : Point,
	A <> B ->
	(OpenRay A B C) \/
	(Distance A B = Distance A C) \/
	(EquiOriented A B A C) ->
	A <> C.
Proof.
	intros A B C H [H0| [H1| H2]].
	 apply (OpenRayDistinct A B C H H0).
	 apply (DistinctEqDistanceDistinct A B A C H H1).
	 apply (EquiOrientedDistinct A B A C H H2).
Qed.

Lemma EquiOrientedCollinearBCDCollinearABC : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear B C D ->
	Collinear A B C.
Proof.
	intros; split.
	 immediate2.
	 intro; assert (EquiOriented B A D C).
	  apply ChangeSide.
	   apply ChangeAll.
	    trivial.
	    immediate2.
	    intuition.
	   apply (EquiOrientedDistinct A B); immediate2.
	  contradict1 H1 H2.
Qed.

Lemma EquiOrientedCollinearABDCollinearABC : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A B D ->
	Collinear A B C.
Proof.
	intros; split.
	 immediate2.
	 intro H1; decompose [or] (FourthPoint B A C D H1).
	  contradict1 H0 H2.
	  contradict1 H H3.
	  setLine0 A B ipattern:ab.
	   immediate2.
	   setCircle0 D A B ipattern:gamma.
	     setInterDiameter ab gamma ipattern:A'.
	     elim (NotClockwiseABA A' D).
	     apply (ChangeSide _ _ _ _ Heo).
	    apply (DistinctEqDistanceDistinct A B D A'); immediate2.
	    step2 H.
	      step2 Heo.
	      apply (DistinctEqDistanceDistinct A B D A'); immediate2.
Qed.

Lemma EquiOrientedCollinearACDCollinearABC : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A C D ->
	Collinear A B C.
Proof.
	intros; split.
	 immediate2.
	 intro; elim (ClockwiseBACNotCollinear _ _ _ H1).
	   apply (EquiOrientedCollinearBCDCollinearABC _ _ _ _ H).
	   apply CollinearCBA; apply (EquiOrientedCollinearABDCollinearABC D C B A).
	  step2 H.
	  immediate2.
Qed.

Lemma EquiOrientedCollinearBCDCollinearABD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear B C D ->
	Collinear A B D.
Proof.
	intros; from2 H (EquiOriented B A D C).
	   apply (EquiOrientedCollinearBCDCollinearABC _ _ _ _ H H0).
	 apply CollinearBAC; apply (EquiOrientedCollinearACDCollinearABC _ _ _ _ H1).
	   immediate2.
Qed.

Lemma EquiOrientedCollinearABCCollinearABD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A B C ->
	Collinear A B D.
Proof.
	intros;from2 H (EquiOriented B A D C).
	 apply CollinearBAC; apply (EquiOrientedCollinearABDCollinearABC _ _ _ _ H1).
	   immediate2.
Qed.

Lemma EquiOrientedCollinearACDCollinearABD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A C D ->
	Collinear A B D.
Proof.
	intros;from2 H (EquiOriented B A D C).
	   apply (EquiOrientedCollinearACDCollinearABC _ _ _ _ H H0).
	 apply CollinearBAC; apply (EquiOrientedCollinearBCDCollinearABC _ _ _ _ H1).
	   immediate2.
Qed.

Lemma EquiOrientedCollinearBCDCollinearACD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear B C D ->
	Collinear A C D.
Proof.
	intros; split.
	 intro H1; decompose [or] (FourthPoint A C D B H1).
	  elim (ClockwiseBACNotCollinear _ _ _ H2).
	    apply CollinearCAB;
	     apply (EquiOrientedCollinearBCDCollinearABC _ _ _ _ H H0).
	  elim (ClockwiseABCNotCollinear _ _ _ H3).
	    apply (EquiOrientedCollinearBCDCollinearABD _ _ _ _ H H0).
	  contradict1 H0 H3.
	 intro H1; decompose [or] (FourthPoint C A D B H1).
	  elim (ClockwiseABCNotCollinear _ _ _ H2).
	    apply CollinearCAB;
	     apply (EquiOrientedCollinearBCDCollinearABC _ _ _ _ H H0).
	  contradict1 H0 H3.
	  elim (ClockwiseBACNotCollinear _ _ _ H3).
	    apply (EquiOrientedCollinearBCDCollinearABD _ _ _ _ H H0).
Qed.

Lemma EquiOrientedCollinearABCCollinearACD : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B C ->
	Collinear A C D.
Proof.
	intros.
	apply CollinearCBA; apply (EquiOrientedCollinearBCDCollinearABD D C B A).
	 step2 H.
	 immediate2.
Qed.

Lemma EquiOrientedCollinearABDCollinearACD : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B D ->
	Collinear A C D.
Proof.
	intros.
	apply CollinearCBA; apply (EquiOrientedCollinearACDCollinearABD D C B A).
	 step2 H.
	 immediate2.
Qed.

Lemma EquiOrientedCollinearACDCollinearBCD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A C D ->
	Collinear B C D.
Proof.
	intros;from2 H (EquiOriented B A D C).
	   apply (EquiOrientedCollinearACDCollinearABC _ _ _ _ H H0).
	 apply CollinearACB; apply (EquiOrientedCollinearBCDCollinearACD _ _ _ _ H1).
	   immediate2.
Qed.

Lemma EquiOrientedCollinearABCCollinearBCD : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B C ->
	Collinear B C D.
Proof.
	intros.
	apply CollinearCBA; apply (EquiOrientedCollinearBCDCollinearABC D C B A).
	 step2 H.
	 immediate2.
Qed.

Lemma EquiOrientedCollinearABDCollinearBCD : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B D ->
	Collinear B C D.
Proof.
	intros.
	apply CollinearCBA; apply (EquiOrientedCollinearACDCollinearABC D C B A).
	 step2 H.
	 immediate2.
Qed.

Lemma EquiOrientedCollinearCollinearABC : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear B C D \/ Collinear A B D\/ Collinear A C D ->
	Collinear A B C.
Proof.
	intuition.
	 apply (EquiOrientedCollinearBCDCollinearABC _ _ _ _ H H1).
	 apply (EquiOrientedCollinearABDCollinearABC _ _ _ _ H H0).
	 apply (EquiOrientedCollinearACDCollinearABC _ _ _ _ H H0).
Qed.

Lemma EquiOrientedCollinearCollinearABD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A B C  \/ Collinear A C D \/ Collinear B C D ->
	Collinear A B D.
Proof.
	intuition.
	 apply (EquiOrientedCollinearABCCollinearABD _ _ _ _ H H1).
	 apply (EquiOrientedCollinearACDCollinearABD _ _ _ _ H H0).
	 apply (EquiOrientedCollinearBCDCollinearABD _ _ _ _ H H0).
Qed.

Lemma EquiOrientedCollinearCollinearACD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear B C D  \/ (A<>B /\ Collinear A B C) \/ (A<>B /\ Collinear A B D) ->
	Collinear A C D.
Proof.
	intuition.
	 apply (EquiOrientedCollinearBCDCollinearACD _ _ _ _ H H1).
	 apply (EquiOrientedCollinearABCCollinearACD _ _ _ _ H H1 H2).
	 apply (EquiOrientedCollinearABDCollinearACD _ _ _ _ H H1 H2).
Qed.

Lemma EquiOrientedCollinearCollinearBCD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A C D  \/ (A<>B /\ Collinear A B C) \/ (A<>B /\ Collinear A B D) ->
	Collinear B C D.
Proof.
	intuition.
	 apply (EquiOrientedCollinearACDCollinearBCD _ _ _ _ H H1).
	 apply (EquiOrientedCollinearABCCollinearBCD _ _ _ _ H H1 H2).
	 apply (EquiOrientedCollinearABDCollinearBCD _ _ _ _ H H1 H2).
Qed.

Lemma TwoPointsOnLineOrientation : forall A B : Point, forall l : Line, 
	OnLine l A ->
	OnLine l B ->
	EquiOriented A B (LineA l) (LineB l) \/ EquiOriented A B (LineB l) (LineA l).
Proof.
	intros; destruct l; simplLine1.
	by2Cases1 H.
	 assert (Collinear A0 A B).
	  canonize1.
	   elim H.
	     step2 H1.
	   elim H4.
	     step2 H1.
	  by2Cases1 H2.
	   since2 (Collinear A B A0).
	    by2Cases1 H4.
	     right; canonize1.
	       step2 H1.
	       step2 H5.
	     left; canonize1.
	       step2 H1.
	       step2 H3.
	      apply (OpenRayDistinct A0 B0 A); immediate2.
	      step2 H5.
	   right; canonize1.
	     step2 H1.
	     step2 H3.
	     apply sym_not_eq; apply (OpenRayDistinct A0 B0 A); immediate2.
	 assert (Collinear B0 A B).
	  canonize1.
	   elim H4; step2 H1.
	   elim H; step2 H1.
	  by2Cases1 H2.
	   since2 (Collinear A B B0).
	    by2Cases1 H4.
	     left; canonize1.
	       step2 H1.
	       step2 H5.
	     right; canonize1.
	       step2 H1.
	       step2 H3.
	      apply (OpenRayDistinct B0 A0 A); immediate2.
	      step2 H5.
	   left; canonize1.
	     step2 H1.
	     step2 H3.
	     apply sym_not_eq; apply (OpenRayDistinct B0 A0 A); immediate2.
Qed.

Lemma OnLine3 : forall d : Line, forall A B C : Point,
	OnLine d A ->
	OnLine d B ->
	OnLine d C ->
	Collinear A B C.
Proof.
	destruct d; simplLine1; intros.
	destruct (Apart A B A0 n).
	 from2 H (Collinear A0 A B0).
	   from2 H (Collinear A0 A C).
	   step1 H3.
	 from2 H (Collinear A0 B B0).
	   from2 H (Collinear A0 B C).
	   step1 H3.
Qed.

End SECOND_DIMENSION.
