Require Import A1_Plan A2_Orientation A7_Tactics.
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp.

Section BETWEEN_PROP.

Lemma BetweenCollinear : forall A B C : Point,
	Between A B C -> Collinear A B C.
Proof.
	intros A B C (H, H0).
	apply (EquiOrientedCollinearBC _ _ _ H0).
Qed.

Lemma BetweenDistinctAB : forall A B C : Point,
	Between A B C -> A <> B.
Proof.
	canonize1.
Qed.

Lemma BetweenOpenRayAB : forall A B C : Point,
	Between A B C -> OpenRay A B C.
Proof.
	intros.
	decompose [or] (CollinearTwoCases A B C (BetweenCollinear A B C H)).
	 trivial.
	 destruct H; simplGoal0.
	   elim (ClockwiseNotClockwise _ _ _ H2).
	   apply (ChangeSide _ _ _ _ H1 H).
	   unfold OpenRay in H0; apply (ChangeSense _ _ _ _ H0).
	  apply CollinearABA.
	  trivial.
Qed.

Lemma BetweenOpenRayAC : forall A B C : Point,
	Between A B C -> OpenRay A C B.
Proof.
	intros; apply OpenRaySym.
	 canonize1.
	 apply BetweenOpenRayAB; trivial.
Qed.

Lemma BetweenOpenRayCB : forall A B C : Point,
	Between A B C -> OpenRay C B A.
Proof.
	intros.
	decompose [or] (CollinearTwoCases C B A (CollinearCBA _ _ _ (BetweenCollinear A B C H))).
	 trivial.
	 destruct H; simplGoal0.
	   elim (ClockwiseNotClockwise _ _ _ H2).
	   apply H1.
	   unfold OpenRay in H0; apply (ChangeSense _ _ _ _ H0).
	  apply CollinearABA.
	  trivial.
Qed.

Lemma OpenRayBetween : forall A B C D : Point,
	OpenRay B C D ->
	Between A B C ->
	Between A B D.
Proof.
	canonize1.
Qed.

Lemma TwoSidesLine : forall A B C D E : Point,
	Clockwise A E D ->
	Collinear D E B ->
	Between A B C ->
	Clockwise C D E.
Proof.
	intros.
	decompose [or] (CollinearTwoCases D E B H0).
	 canonize1.
	   apply ClockwiseCAB; apply (ChangeAll _ _ _ _ H2).
	  apply sym_not_eq; apply (ClockwiseDistinctBC _ _ _ H).
	  left; apply CollinearABA.
	  apply ClockwiseCAB; apply H5.
	    apply ClockwiseCAB; apply (ChangeSense _ _ _ _ H2).
	   apply CollinearABA.
	   apply ClockwiseBCA; trivial.
	 canonize1.
	   apply ClockwiseCAB; apply (ChangeSide _ _ _ _ H2).
	  apply (ClockwiseDistinctBC _ _ _ H).
	  apply ClockwiseBCA; apply (ChangeSense _ _ _ _ H5).
	   apply CollinearABB.
	   apply ClockwiseBCA; apply H2.
	     apply ClockwiseBCA; trivial.
Qed.

Lemma SegmentABA : forall A B : Point, Segment  A B A.
Proof.
	canonize1.
	elim (NotClockwiseAAB _ _ H).
Qed.

Lemma SegmentABB : forall A B : Point, Segment  A B B.
Proof.
	canonize1.
	elim (NotClockwiseAAB _ _ H).
Qed.

Lemma SegmentSym : forall A B C : Point,
	Segment A B C -> Segment B A C.
Proof.
	canonize1.
Qed.

Lemma SegmentCollinear : forall A B C : Point,
	Segment A C B -> Collinear A B C.
Proof.
	canonize1.
	 elim (NotClockwiseABB A C); auto.
	 elim (NotClockwiseABB C A); apply H1.
	   apply ClockwiseCAB; trivial.
Qed.

Lemma SegmentOpenRayAC : forall A B C : Point,
	Segment A B C ->
	OpenRay A C B.
Proof.
	canonize1.
Qed.

Lemma SegmentOpenRayAB : forall A B C : Point,
	Segment A B C ->
	A <> C ->
	OpenRay A B C.
Proof.
	canonize1.
	apply (ChangeAllABAC _ _ _ H1 H0).
	exact H.
Qed.

Lemma BetweenSegment : forall A B C : Point,
	Between A B C -> Segment A C B.
Proof.
	intros; split.
	 apply (BetweenOpenRayAB _ _ _ H).
	 apply (BetweenOpenRayCB _ _ _ H).
Qed.

Lemma SegmentBetween : forall A B C : Point,
	Segment A C B ->
	A <> B ->
	B <> C ->
	Between A B C.
Proof.
	canonize1.
	apply (ChangeSide _ _ _ _ H3); auto.
Qed.

Lemma EquiOrientedSegment : forall A B C : Point,
	EquiOriented A B B C -> Segment A C B.
Proof.
	intros; destruct (CollinearTwoCases C B A).
	 apply CollinearCBA; apply (EquiOrientedCollinearBC _ _ _ H).
	 canonize1.
	   apply (ChangeSenseABAC _ _ _ H0); auto.
	 canonize1.
	  elim (ClockwiseNotClockwise _ _ _ H1); auto.
	  elim (ClockwiseNotClockwise _ _ _ H1); apply H.
	    apply (ChangeSenseABAC _ _ _ H0); auto.
Qed.

Lemma EquiOrientedClosedRaySegment : forall A B C D : Point,
	EquiOriented C D A B ->
	ClosedRay A B C ->
	Segment A D C.
Proof.
	canonize1.
	 decompose [or] (FourthPoint A C M D H1).
	  elim (NotClockwiseABA A B).
	    apply H; apply (ClockwiseBCA _ _ _ H2).
	  trivial.
	  elim (ClockwiseNotClockwise _ _ _ (H0 M H1)).
	    apply (ChangeSense _ _ _ _ H).
	   canonize1.
	    elim (NotClockwiseABA A B); auto.
	    elim (NotClockwiseABA D C).
	      apply (ChangeSide _ _ _ _ H).
	     apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H2).
	     apply (ChangeSenseABAC _ _ _ H0).
	      apply (ClockwiseBCA _ _ _ H2).
	   trivial.
	 decompose [or] (FourthPoint D C M A H1).
	  elim (NotClockwiseABA D C).
	    apply (ChangeSide _ _ _ _ H).
	   apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H2).
	   apply (ChangeSenseABAC _ _ _ H0).
	    apply (ClockwiseBCA _ _ _ H2).
	  trivial.
	  elim (ClockwiseNotClockwise _ _ _ (H0 M H3)).
	    apply (ChangeSense _ _ _ _ H).
	   canonize1.
	    elim (NotClockwiseABA A B); auto.
	    elim (NotClockwiseABA D C).
	      apply (ChangeSide _ _ _ _ H).
	     apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H2).
	     apply (ChangeSenseABAC _ _ _ H0).
	      apply (ClockwiseBCA _ _ _ H2).
	   trivial.
Qed.

Lemma SegmentTransBDC : forall A B C D : Point,
	Segment A C B ->
	Segment A D C ->
	Segment B D C.
Proof.
	canonize1.
	 decompose [or] (FourthPoint B C M D H0).
	  elim (NotClockwiseABB A D).
	    apply H; apply (ChangeSenseABAC _ _ _ H2).
	   trivial.
	  trivial.
	  elim (ClockwiseNotClockwise _ _ _ H0).
	    apply (ChangeAllABAC _ _ _ H2).
	   apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H0).
	   apply (ChangeSide _ _ _ _ H).
	    intro; subst.
	      elim (NotClockwiseAAB C M); apply (ChangeSenseABAC _ _ _ H1).
	     trivial.
	    auto.
	 decompose [or] (FourthPoint D C M B H0).
	  elim (NotClockwiseABB A D); apply H; apply H1.
	    apply ClockwiseBCA; auto.
	  trivial.
	  elim (ClockwiseNotClockwise _ _ _ H0).
	    apply (ChangeSide _ _ _ _ H3).
	   apply (ClockwiseDistinctAB _ _ _ H0).
	   apply H; apply (ChangeSenseABAC _ _ _ H2).
	    trivial.
Qed.

Lemma SegmentTransADB : forall A B C D : Point,
	Segment A C B ->
	Segment A D C ->
	Segment A D B.
Proof.
	canonize1.
	decompose [or] (FourthPoint D B M C H0).
	 elim (NotClockwiseABB A D).
	   apply H; apply (ChangeSenseABAC _ _ _ H2).
	  apply (ClockwiseBCA _ _ _ H4).
	 auto.
	 apply (ChangeSenseABAC _ _ _ H).
	  auto.
Qed.

End BETWEEN_PROP.
