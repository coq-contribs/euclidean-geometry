Section PERPENDICULAR_LINES.

Inductive Perpendicular (l1 l2 : Line) : Prop :=
	| PerpRightAngle : forall A B C : Point, RightAngle A B C ->
				OnLine l1 A -> OnLine l1 B ->
				OnLine l2 B -> OnLine l2 C ->
				Perpendicular l1 l2.

Lemma PerpendicularSym : forall l1 l2 : Line,
	Perpendicular l1 l2 -> Perpendicular l2 l1.
Proof.
	intros; inversion H.
	apply (PerpRightAngle l2 l1 C B A); immediate11.
Qed.

Lemma EqEqPerpendicular : forall l1 l2 l3 l4 : Line,
	EqLine l1 l2 ->
	EqLine l3 l4 ->
	Perpendicular l1 l3 ->
	Perpendicular l2 l4.
Proof.
	intros.
	inversion H1.
	apply (PerpRightAngle l2 l4 A B C).
	 immediate11.
	 apply (EqLineOnLine l1); immediate11.
	 apply (EqLineOnLine l1); immediate11.
	 apply (EqLineOnLine l3); immediate11.
	 apply (EqLineOnLine l3); immediate11.
Qed.

Lemma PerpendicularSecant : forall l1 l2 : Line,
	Perpendicular l1 l2 -> SecantLines l1 l2.
Proof.
	intros; inversion H.
	apply (TwoPointsSecantLine l1 l2 B A).
	 immediate11.
	 immediate11.
	 immediate11.
	 intro.
	   assert (Collinear A B C).
	  step11 l2.
	  unfold RightAngle in H0.
	    assert (Collinear Uu Oo Vv).
	   step11 H0.
	   assert (Clockwise Oo Vv Uu).
	    immediate11.
	    contradict1 H7 H8.
Qed.

Definition PerpendicularPoint : forall l1 l2 : Line, 
	Perpendicular l1 l2 -> Point.
Proof.
	intros.
	setInterLinesPoint4 l1 l2 ipattern:M.
	 apply PerpendicularSecant; immediate11.
	 exact M.
Defined.

Lemma PerpendicularPointOnLine1 : forall l1 l2 : Line, forall Hp : Perpendicular l1 l2,
	OnLine l1 (PerpendicularPoint l1 l2 Hp).
Proof.
	intros.
	unfold PerpendicularPoint in |- *.
	immediate11.
Qed.

Lemma PerpendicularPointOnLine2 : forall l1 l2 : Line, forall Hp : Perpendicular l1 l2,
	OnLine l2 (PerpendicularPoint l1 l2 Hp).
Proof.
	intros.
	unfold PerpendicularPoint in |- *.
	immediate11.
Qed.

Lemma UniquePerpendicularPoint : forall M : Point, forall d1 d2 : Line, forall Hp : Perpendicular d1 d2,
	OnLine d1 M ->
	OnLine d2 M ->
	M = PerpendicularPoint d1 d2 Hp.
Proof.
	intros; unfold PerpendicularPoint in |- *.
	immediate11.
Qed.

Lemma  PerpendicularRightAngle : forall l1 l2 : Line, forall Hp : Perpendicular l1 l2,
	forall A B : Point,
	A <> PerpendicularPoint l1 l2 Hp ->
	B <> PerpendicularPoint l1 l2 Hp ->
	OnLine l1 A ->
	OnLine l2 B ->
	RightAngle A (PerpendicularPoint l1 l2 Hp) B.
Proof.
	intros.
	inversion Hp.
	assert (B0 = PerpendicularPoint l1 l2 Hp).
	 unfold PerpendicularPoint in |- *.
	   immediate11.
	 rewrite <- H8; rewrite <- H8 in H; rewrite <- H8 in H0.
	   assert (Collinear A A0 B0).
	  step11 l1.
	  assert (Collinear B B0 C).
	   step11 l2.
	   by3SegmentCases1 H9; by3SegmentCases1 H10.
	    from11 H12 (CongruentAngle A B0 C A B0 B).
	     step11 H13.
	       from11 H11 (Between A B0 A0).
	      as11 (Supplement A B0 C A0 B0 C).
	    from11 H13 (CongruentAngle A B0 C A B0 B).
	      step11 H12.
	      from11 H11 (Between A B0 A0).
	     as11 (Supplement A B0 C A0 B0 C).
	    since11 (OpposedAngles B0 A0 C A B).
	     from11 H11 (Between A B0 A0).
	      from11 H13 (Between C B0 B).
	     step11 H3.
	    from11 H12 (CongruentAngle A0 B0 C A B0 B).
	     step11 H11.
	       immediate11.
	     step11 H13.
	    from11 H12 (CongruentAngle A0 B0 C A B0 B).
	      step11 H11.
	    from11 H12 (CongruentAngle A0 B0 B A B0 B).
	      step11 H11.
	      from11 H13 (Between C B0 B).
	     as11 (Supplement A0 B0 B A0 B0 C).
	    from11 H12 (CongruentAngle A0 B0 C A B0 B).
	     step11 H13.
	    from11 H12 (CongruentAngle A0 B0 C A B0 B).
	     step11 H11.
	    from11 H12 (CongruentAngle A0 B0 B A B0 B).
	     step11 H11.
	       from11 H13 (Between C B0 B).
	      as11 (Supplement A0 B0 B A0 B0 C).
Qed.

Lemma  PointsPerpendicularRightAngle : forall A B C : Point, forall l1 l2 : Line,
	Perpendicular l1 l2 ->
	A <> B ->
	C <> B ->
	OnLine l1 A ->
	OnLine l1 B ->
	OnLine l2 B ->
	OnLine l2 C ->
	RightAngle A B C.
Proof.
	intros.
	assert (B = PerpendicularPoint l1 l2 H).
	 apply UniquePerpendicularPoint; immediate11.
	 subst.
	   apply PerpendicularRightAngle; immediate11.
Qed.

Lemma PerpendicularMidLine : forall A B : Point, forall Hab : A <> B,
	Perpendicular (Ruler A B Hab) (MidLine A B Hab).
Proof.
	intros; apply (PerpRightAngle (Ruler A B Hab) (MidLine A B Hab) A  (MidPoint A B Hab) (LineA (MidLine A B Hab))).
	 immediate11.
	 immediate11.
	 since11 (Collinear A B (MidPoint A B Hab)).
	 immediate11.
	 immediate11.
Qed.

End PERPENDICULAR_LINES.
