Section RAYS_PROP.

Lemma OpenRayAAB : forall A B : Point,
	OpenRay A A B.
Proof.
	canonize1.
	elim (NotClockwiseAAB _ _ H).
Qed.

Lemma OpenRayABB : forall A B : Point,
	OpenRay A B B.
Proof.
	canonize1.
Qed.

Lemma OpenRayCollinear : forall A B C : Point,
	OpenRay A B C -> Collinear A B C.
Proof.
	intros; unfold OpenRay in *.
	apply (EquiOrientedCollinearAC _ _ _ H).
Qed.

Lemma OpenRayTrans : forall A B C D : Point,
	OpenRay A B C -> OpenRay A C D -> OpenRay A B D.
Proof.
	canonize1.
Qed.

Lemma ThreeCases : forall A B C : Point,
	Clockwise A B C \/ Clockwise B A C \/ Collinear A B C.
Proof.
	intros; decompose [or] (FourCases A B C).
	 auto.
	 auto.
	 do 2 right; apply OpenRayCollinear; trivial.
	 do 2 right; apply CollinearBAC; apply OpenRayCollinear; trivial.
Qed.

Lemma OnOrNotOnLine : forall l : Line, forall M : Point,
	OnLine l M \/ ~OnLine l M.
Proof.
	destruct l; simplLine1; intros.
	decompose [or] (ThreeCases A B M).
	 right; apply (ClockwiseABCNotCollinear A B M H).
	 right; apply (ClockwiseBACNotCollinear A B M H0).
	 left; exact H0.
Qed.

Lemma CollinearTwoCases : forall A B C : Point,
	Collinear A B C -> OpenRay A B C \/ OpenRay B A C.
Proof.
	intros; decompose [or] (FourCases A B C).
	 elim (ClockwiseABCNotCollinear _ _ _ H0 H).
	 elim (ClockwiseABCNotCollinear _ _ _ H1).
	   apply (CollinearBAC _ _ _ H).
	 intuition.
	 intuition.
Qed.

Lemma NotClockwiseTwoCases : forall A B C : Point,
	~Clockwise A B C -> Clockwise B A C \/ Collinear A B C.
Proof.
	intros; decompose [or] (ThreeCases A B C); intuition.
Qed.

Lemma NotCollinearTwoCases : forall A B C : Point,
	~Collinear A B C ->
	Clockwise A B C \/ Clockwise B A C.
Proof.
	intros; decompose [or] (ThreeCases A B C); intuition.
Qed.

Lemma CollinearThreeCases : forall A B C : Point,
	Collinear A B C ->
	Segment A B C \/ Segment B C A \/ Segment C A B.
Proof.
	intros.
	assert (H0 := CollinearTwoCases A B C H).
	assert (H1 := CollinearTwoCases B C A (CollinearBCA _ _ _ H)).
	assert (H2 := CollinearTwoCases C A B (CollinearCAB _ _ _ H)).
	unfold Segment in |- *; intuition.
	 left; canonize1.
	   elim (ClockwiseNotClockwise _ _ _ H).
	   apply (ChangeSenseABAC _ _ _ H3).
	   apply H0.
	   apply (ChangeSenseABAC _ _ _ H1).
	   trivial.
	 left; canonize1.
	   elim (ClockwiseNotClockwise _ _ _ H).
	   apply (ChangeSenseABAC _ _ _ H3).
	   apply H1.
	   apply (ChangeSenseABAC _ _ _ H0); trivial.
Qed.

Lemma ClosedRayCollinear : forall A B C : Point,
	ClosedRay A B C -> Collinear A B C.
Proof.
	intros; apply CollinearACB.
	apply (OpenRayCollinear _ _ _ H).
Qed.

Lemma ClosedRayOpenRay : forall A B C : Point,
	ClosedRay A B C -> OpenRay A C B.
Proof.
	canonize1; trivial.
Qed.

Lemma OpenRayClosedRay : forall A B C : Point,
	OpenRay A B C -> ClosedRay A C B.
Proof.
	canonize1.
Qed.

Lemma OpenRaySym : forall A B C : Point,
	A <> B -> OpenRay A B C -> OpenRay A C B.
Proof.
	intros; unfold OpenRay in *.
	apply (ChangeAllABAC _ _ _ H0 H).
Qed.

Lemma EquiOrientedClosedRayClosedRay : forall A B C D : Point,
	EquiOriented C D A B ->
	ClosedRay A B C ->
	ClosedRay A B D.
Proof.
	canonize1.
	decompose [or] (FourthPoint A D M C H1).
	 elim (NotClockwiseABA A B).
	   elim (NotClockwiseABA D C).
	   apply (ChangeSide _ _ _ _ H).
	  apply sym_not_eq; apply (ClockwiseDistinctBC _ _ _ H2).
	  apply (ChangeSense _ _ _ _ H0).
	   apply CollinearABA.
	   apply (ClockwiseCAB _ _ _ H2).
	 auto.
	 auto.
Qed.

Lemma CollinearTrans : forall A B C D : Point,
	A <> B ->
	Collinear A B C ->
	Collinear A B D ->
	Collinear A C D.
Proof.
	intros.
	destruct (CollinearTwoCases A B C H0); destruct (CollinearTwoCases A B D H1);
	 canonize1.
	 elim H5; apply (ChangeSide _ _ _ _ H3 H).
	   apply (ClockwiseCAB _ _ _ H1).
	 elim H6; apply (ChangeSide _ _ _ _ H2 H).
	   exact H1.
	 elim H0; apply (ChangeAll _ _ _ _ H2 H).
	  left; apply CollinearABA.
	  exact H1.
	 elim H6; apply (ChangeSide _ _ _ _ H2 H).
	   exact H1.
	 elim H5; apply (ChangeSide _ _ _ _ H3 H).
	   apply (ClockwiseCAB _ _ _ H1).
	 elim H4; apply (ChangeAll _ _ _ _ H3 H).
	  left; apply CollinearABA.
	  apply (ClockwiseBCA _ _ _ H1).
	 decompose [or] (FourCases C D B); canonize1.
	  elim H6; apply (ChangeAll _ _ _ _ H2 (sym_not_eq H)).
	   left; apply CollinearABA.
	   apply (ClockwiseCAB _ _ _ H7).
	  elim H5; apply (ChangeAll _ _ _ _ H3 (sym_not_eq H)).
	   left; apply CollinearABA.
	   apply (ClockwiseCAB _ _ _ H8).
	  elim H5; apply ClockwiseBCA.
	    apply H7; apply (ClockwiseBCA _ _ _ H1).
	  elim H0; apply ClockwiseCAB.
	    apply (ChangeSense _ _ _ _ H7).
	   apply CollinearABA.
	   apply (ClockwiseBCA _ _ _ H1).
	 decompose [or] (FourCases C D B); canonize1.
	  elim H6; apply (ChangeAll _ _ _ _ H2 (sym_not_eq H)).
	   left; apply CollinearABA.
	   apply (ClockwiseCAB _ _ _ H7).
	  elim H5; apply (ChangeAll _ _ _ _ H3 (sym_not_eq H)).
	   left; apply CollinearABA.
	   apply (ClockwiseCAB _ _ _ H8).
	  elim H4; apply ClockwiseCAB.
	    apply (ChangeSense _ _ _ _ H7).
	   apply CollinearABA.
	   apply (ClockwiseCAB _ _ _ H1).
	  elim H6; apply ClockwiseBCA.
	    apply H7; apply (ClockwiseCAB _ _ _ H1).
Qed.

End RAYS_PROP.
