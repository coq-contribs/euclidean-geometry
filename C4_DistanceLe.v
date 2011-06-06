Section DISTANCE_LE.

Definition DistanceLe := fun M N : Point => Segment Oo N M.

Lemma DistanceLeRefl : forall A : Point, DistanceLe A A.
Proof.
	unfold DistanceLe in |- *; intros.
	immediate1.
Qed.

Lemma DistanceLeOo : forall A : Point, DistanceLe Oo A.
Proof.
	unfold DistanceLe in |- *; intros.
	immediate1.
Qed.

Lemma SegmentDistanceLe : forall A B C : Point,
	Segment A B C ->
	DistanceLe (Distance A C) (Distance A B).
Proof.
	intros; unfold DistanceLe in |- *.
	apply (EquiDistantSegment A B C Oo (Distance A B) (Distance A C) Uu).
	 trivial.
	 apply EquiDistantSym; apply EquiDistantDistance.
	 apply EquiDistantSym; apply EquiDistantDistance.
	 immediate1.
	 apply IsDistanceDistance.
	 apply IsDistanceDistance.
Qed.

Lemma DistanceLeSegment : forall A B C D : Point,
	DistanceLe (Distance A C) (Distance A B) ->
	A <> D ->
	ClosedRay A D B ->
	ClosedRay A D C ->
	Segment A B C.
Proof.
	unfold DistanceLe in |- *; intros.
	apply (EquiDistantSegment Oo (Distance A B) (Distance A C) A B C D).
	 trivial.
	 apply EquiDistantDistance.
	 apply EquiDistantDistance.
	 trivial.
	 trivial.
	 trivial.
Qed.

Lemma DistanceLeTrans : forall A B C : Point,
	DistanceLe A B ->
	DistanceLe B C ->
	DistanceLe A C.
Proof.
	unfold DistanceLe in |- *; intros.
	apply (SegmentTransADB Oo A B C); trivial.
Qed.

Lemma DistanceLeDistancePlus : forall A B : Point,
	IsDistance A ->
	DistanceLe A (DistancePlus A B).
Proof.
	intros; unfold DistanceLe in |- *.
	pattern A at 2 in |- *; rewrite <- (IsDistanceEqDistance A H).
	rewrite DistancePlusOoM; apply IsDistanceSegmentDistancePlus.
	apply IsDistanceDistance.
Qed.

Lemma DistanceLeDistancePlusDistance : forall A B C: Point,
	DistanceLe (Distance A B) (DistancePlus (Distance A B) C).
Proof.
	intros; apply DistanceLeDistancePlus.
	apply IsDistanceDistance.
Qed.

Lemma DistanceLeDistancePlusDistancePlus : forall A B C: Point,
	DistanceLe (DistancePlus A B) (DistancePlus (DistancePlus A B) C).
Proof.
	intros; apply DistanceLeDistancePlus.
	apply IsDistanceDistancePlus.
Qed.

Lemma LeftRegularDistanceLe : forall A B C : Point,
	DistanceLe A B ->
	DistanceLe (DistancePlus C A) (DistancePlus C B).
Proof.
	intros.
	rewrite (DistancePlusOoN C B).
	rewrite <- (Chasles Oo A B).
	 rewrite DistancePlusAssoc.
	   rewrite <- (DistancePlusOoN C A).
	   apply DistanceLeDistancePlusDistancePlus.
	 exact H.
Qed.

End DISTANCE_LE.
