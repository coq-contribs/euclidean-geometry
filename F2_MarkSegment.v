Section MARK_SEGMENT.

Definition AddSegmentPoint (A B C D E : Point) : 
	A <> B -> Collinear A B C -> Point.
Proof.
	intros.
	setLine0 A B ipattern:ab.
	setCircle0 C D E ipattern:g.
	assert (Diameter ab g).
	 simpl in |- *; immediate4.
	 exact (InterDiameterPoint ab g H1).
Defined.

Definition MarkSegmentPoint (A B C D : Point) : 
	A <> B -> Point.
Proof.
	intros.
	 exact (AddSegmentPoint A B A C D H (CollinearABA A B)).
Defined.

Definition OppSegmentPoint (A B C D : Point) : 
	A <> B -> Point.
Proof.
	intros.
	 exact (AddSegmentPoint B A A C D (sym_not_eq H) (CollinearABB B A)).
Defined.

Definition SymmetricPoint (A B : Point) : 
	A <> B -> Point.
Proof.
	intros H.
	 exact (AddSegmentPoint A B B A B H (CollinearABB A B)).
Defined.

Lemma EquiOrientedAddSegmentPoint : forall A B C D E : Point, forall (H : A <> B) (H0 : Collinear A B C),
	EquiOriented C (AddSegmentPoint A B C D E H H0) A B.
Proof.
	intros; unfold AddSegmentPoint in |- *.
	assert (H1 := EquiOrientedInterDiameterPoint (Ruler A B H) (Compass C D E) H0); immediate4.
Qed.
 
Lemma EqDistanceAddSegmentPoint :  forall A B C D E : Point, forall (H : A <> B) (H0 : Collinear A B C),
	Distance C (AddSegmentPoint A B C D E H H0) = Distance D E.
Proof.
	intros; unfold AddSegmentPoint in |- *.
	assert (H1 := EqDistanceInterDiameterPoint (Ruler A B H) (Compass C D E) H0); immediate4.
Qed.
 
Lemma CollinearAddSegmentPoint :  forall A B C D E : Point, forall (H : A <> B) (H0 : Collinear A B C),
	Collinear A B (AddSegmentPoint A B C D E H H0).
Proof.
	intros; unfold AddSegmentPoint in |- *.
	assert (H1 := OnLineInterDiameterPoint (Ruler A B H) (Compass C D E) H0).
	immediate4.
Qed.

Lemma UniqueAddSegmentPoint : forall A B C D E : Point, forall (H : A <> B) (H0 : Collinear A B C), forall M : Point,
	EquiOriented C M A B -> Distance C M = Distance D E ->
	M = AddSegmentPoint A B C D E H H0.
Proof.
	intros; unfold AddSegmentPoint in |- *.
	assert (H3 := UniqueInterDiameterPoint (Ruler A B H) (Compass C D E) H0);
	 simpl in H3; apply H3; immediate4.
Qed.

Lemma ClosedRayMarkSegmentPoint : forall A B C D : Point, forall (H : A <> B),
	ClosedRay A B (MarkSegmentPoint A B C D H).
Proof.
	intros; unfold MarkSegmentPoint in |- *.
	assert (H1 := EquiOrientedAddSegmentPoint A B A C D H (CollinearABA A B)); immediate4.
Qed.
 
Lemma EqDistanceMarkSegmentPoint :  forall A B C D : Point, forall (H : A <> B),
	Distance A (MarkSegmentPoint A B C D H) = Distance C D.
Proof.
	intros; unfold MarkSegmentPoint in |- *.
	assert (H1 := EqDistanceAddSegmentPoint A B A C D H (CollinearABA A B)); immediate4.
Qed.

Lemma UniqueMarkSegmentPoint : forall A B C D : Point, forall (H : A <> B), forall M : Point,
	ClosedRay A B M -> Distance A M = Distance C D ->
	M = MarkSegmentPoint A B C D H.
Proof.
	intros; unfold MarkSegmentPoint in |- *.
	apply UniqueAddSegmentPoint; immediate4.
Qed.

Lemma SegmentOppSegmentPoint : forall A B C D : Point, forall (H : A <> B),
	Segment (OppSegmentPoint A B C D H) B A.
Proof.
	intros; unfold OppSegmentPoint in |- *.
	assert (H1 := EquiOrientedAddSegmentPoint B A A C D (sym_not_eq H) (CollinearABB B A)).
	apply EquiOrientedSegment.
	immediate4.
Qed.
 
Lemma EqDistanceOppSegmentPoint :  forall A B C D : Point, forall (H : A <> B),
	Distance A (OppSegmentPoint A B C D H) = Distance C D.
Proof.
	intros; unfold OppSegmentPoint in |- *.
	assert (H1 := EqDistanceAddSegmentPoint B A A C D (sym_not_eq H) (CollinearABB B A)); immediate4.
Qed.

Lemma UniqueOppSegmentPoint : forall A B C D : Point, forall (H : A <> B), forall M : Point,
	Segment B M A -> Distance A M = Distance C D ->
	M = OppSegmentPoint A B C D H.
Proof.
	intros; unfold OppSegmentPoint in |- *.
	apply UniqueAddSegmentPoint.
	 canonize1.
	   step4 H2.
	   step4 H3.
	 immediate4.
Qed.

Lemma BetweenSymmetricPoint : forall A B : Point, forall (H : A <> B),
	Between A B (SymmetricPoint A B H).
Proof.
	intros; unfold SymmetricPoint in |- *.
	assert (H1 := EquiOrientedAddSegmentPoint A B B A B H (CollinearABB A B)); split; immediate4.
	assert (H2 := EqDistanceAddSegmentPoint A B B A B H (CollinearABB A B));  step4 H2.
Qed.
 
Lemma DistinctBSymmetricPoint : forall A B : Point, forall (H : A <> B),
	B <> SymmetricPoint A B H.
Proof.
	intros; assert (H0 := BetweenSymmetricPoint A B H).
	immediate4.
Qed.
 
Lemma DistinctASymmetricPoint : forall A B : Point, forall (H : A <> B),
	A <> SymmetricPoint A B H.
Proof.
	intros; assert (H0 := BetweenSymmetricPoint A B H).
	immediate4.
Qed.
 

Lemma EqDistanceSymmetricPoint :  forall A B : Point, forall (H : A <> B),
	Distance B (SymmetricPoint A B H) = Distance A B.
Proof.
	intros; unfold SymmetricPoint in |- *.
	assert (H1 := EqDistanceAddSegmentPoint A B B A B H (CollinearABB A B));  immediate4.
Qed.

Lemma UniqueSymmetricPoint : forall A B : Point, forall (H : A <> B), forall M : Point,
	EquiOriented A B B M -> Distance B M = Distance A B ->
	M = SymmetricPoint A B H.
Proof.
	intros; unfold SymmetricPoint in |- *.
	apply UniqueAddSegmentPoint; immediate4.
Qed.

Lemma CaseNullDistance : forall A B I : Point, I <> A -> Distance A B = Oo -> A = B.
Proof.
	intros.
	since4 (Collinear I A A).
	since4 (A = AddSegmentPoint I A A A B H H1).
	 apply UniqueAddSegmentPoint.
	  immediate4.
	  immediate4.
	 rewrite H2; apply sym_eq.
	   apply UniqueAddSegmentPoint.
	  canonize1.
	    since4 (Distance A B <> Oo).
	   apply DistanceNotNull; immediate4.
	   contradict1 H0 H4.
	  immediate4.
Qed.

Lemma NullDistanceEq : forall A B : Point, Distance A B = Oo -> A = B.
Proof.
	intros; destruct (Apart Oo Uu A DistinctOoUu).
	 apply (CaseNullDistance A B Oo); trivial.
	 apply (CaseNullDistance A B Uu); trivial.
Qed.

Lemma DistancePlusRightCancell : forall A B C D : Point,
	DistancePlus (Distance A B) (Distance C D) = Distance A B -> C = D.
Proof.
	intros.
	apply NullDistanceEq.
	apply (DistancePlusNeutralRightEq (Distance A B)); immediate4.
Qed.

Lemma DistancePlusLeftCancell : forall A B C D : Point,
	DistancePlus (Distance C D) (Distance A B) = Distance A B -> C = D.
Proof.
	intros.
	apply (DistancePlusRightCancell A B C D).
	immediate4.
Qed.

End MARK_SEGMENT.

