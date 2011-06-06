Section SUM_OF_DISTANCES.

Definition DistancePlus : forall M N : Point, Point.
Proof.
	intros.
	setCircle0 (Distance Oo M) Oo N ipattern:gamma.
	destruct (InterDiameterPointDef lineOoUu gamma) as (P, ((H1, H2), H3)).
	 assert (H := IsDistanceDistance Oo M).
	   unfold IsDistance in H; simpl in |- *; immediate1.
	 exact P.
Defined.

Ltac destructDistancePlus M N P := unfold DistancePlus;
let H1 := fresh in (
	let H2 := fresh in (
		let H3 := fresh in (
			destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo M) Oo N)
            (ClosedRayCollinear Oo Uu (Distance Oo M)
               (IsDistanceDistance Oo M)))
  			as (P, ((H1, H2), H3)))));
simpl in *.

Lemma IsDistanceDistancePlus : forall M N : Point,
	IsDistance (DistancePlus M N).
Proof.
	intros.
	destructDistancePlus M N ipattern:P.
	unfold IsDistance in |- *; apply (EquiOrientedClosedRayClosedRay _ _ _ _ H0).
	fold (IsDistance (Distance Oo M)) in |- *; apply IsDistanceDistance.
Qed.

Lemma EqDistanceDistancePlus : forall M N : Point,
	Distance Oo (DistancePlus M N) = DistancePlus M N.
Proof.
	intros.
	apply IsDistanceEqDistance.
	apply IsDistanceDistancePlus.
Qed.

Lemma IsDistanceSegmentDistancePlus : forall M N : Point,	
	IsDistance M ->
	Segment Oo (DistancePlus M N) M.
Proof.
	intros.
	destructDistancePlus M N ipattern:P.
	apply (EquiOrientedClosedRaySegment Oo Uu).
	 rewrite (IsDistanceEqDistance M H) in H1; immediate1.
	 fold (IsDistance M) in |- *; trivial.
Qed.

Lemma IsDistancePlusEqDistance : forall M N : Point,
	IsDistance M ->
	IsDistance N ->
	Distance M (DistancePlus M N) = N.
Proof.
	intros.
	destructDistancePlus M N ipattern:P.
	rewrite (IsDistanceEqDistance M H) in H1; rewrite (IsDistanceEqDistance N H0) in H1; immediate1.
Qed.

Lemma DistancePlusOoM : forall M N : Point,
	DistancePlus M N = DistancePlus (Distance Oo M) N.
Proof.
	intros.
	destructDistancePlus M N ipattern:P.
	destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo (Distance Oo M)) Oo N)) as (Q, ((H2, H3), H4)); simpl in *.
	apply H1; split.
	 rewrite <- (EqDistanceDistance Oo M); trivial.
	 rewrite <- (EqDistanceDistance Oo M); trivial.
Qed.

Lemma DistancePlusOoN : forall M N : Point,
	DistancePlus M N = DistancePlus M (Distance Oo N).
Proof.
	intros.
	destructDistancePlus M N ipattern:P.
	destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo M) Oo (Distance Oo N))) as (Q, ((H2, H3), H4)); simpl in *.
	apply H1; split.
	 rewrite H2; apply EqDistanceDistance.
	 trivial.
Qed.

Lemma Chasles : forall A B C : Point,
	Segment A C B ->
	DistancePlus (Distance A B) (Distance B C) = Distance A C.
Proof.
	intros; rewrite <- EqDistanceDistancePlus.
	apply DistanceEq;
	 apply  (EquiDistantChasles Oo (Distance A B) (DistancePlus (Distance A B) (Distance B C)) A B C).
	 apply IsDistanceSegmentDistancePlus; apply IsDistanceDistance.
	 trivial.
	 apply EqDistance.
	   apply IsDistanceEqDistance; apply IsDistanceDistance.
	 apply EqDistance.
	   apply IsDistancePlusEqDistance; apply IsDistanceDistance.
Qed.

Lemma ChaslesRec : forall A B C : Point,
	DistancePlus (Distance A B) (Distance B C) = Distance A C ->
	Segment A C B.
Proof.
	intros.
	apply (ChaslesEquiDistant Oo (Distance A B) (DistancePlus (Distance A B) (Distance B C))).
	 apply IsDistanceSegmentDistancePlus; apply IsDistanceDistance.
	 apply EquiDistantDistance.
	 apply EqDistance.
	   apply IsDistancePlusEqDistance; apply IsDistanceDistance.
	 apply EqDistance.
	   rewrite EqDistanceDistancePlus.
	   trivial.
Qed.

Lemma DistancePlusCommut : forall M N : Point,
	DistancePlus M N = DistancePlus N M.
Proof.
	intros.
	intros; rewrite <- (EqDistanceDistancePlus N M).
	rewrite DistanceSym;
	 rewrite <- (Chasles (DistancePlus N M) (Distance Oo N) Oo).
	 rewrite DistanceSym.
	   rewrite (DistancePlusOoN N M); rewrite (DistancePlusOoM N);
	    rewrite IsDistancePlusEqDistance.
	  rewrite (DistanceSym (Distance Oo N)); repeat rewrite EqDistanceDistance.
	    rewrite <- DistancePlusOoN; apply DistancePlusOoM.
	  apply IsDistanceDistance.
	  apply IsDistanceDistance.
	 rewrite DistancePlusOoM; apply SegmentSym;
	  apply IsDistanceSegmentDistancePlus.
	   apply IsDistanceDistance.
Qed.

Lemma DistancePlusAssoc : forall M N P : Point,  
 	DistancePlus M (DistancePlus N P) = DistancePlus (DistancePlus M N) P.
Proof.
	intros.
	unfold DistancePlus in |- *; simpl in |- *.
	destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo N) Oo P))  as (A, ((H0, H1), H2)).
	destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo M) Oo A))  as (B, ((H3, H4), H5)).
	destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo M) Oo N))  as (C, ((H6, H7), H8)).
	destruct (InterDiameterPointDef lineOoUu (Compass (Distance Oo C) Oo P)) as (D, ((H9, H10), H11)).
	simpl in *.
	assert (ClosedRay Oo Uu C).
	 apply (EquiOrientedClosedRayClosedRay _ _ _ _ H7).
	   apply IsDistanceDistance.
	 apply H5; split.
	  rewrite <- (Chasles Oo (Distance Oo N) A).
	   rewrite H0; rewrite EqDistanceDistance.
	     rewrite <- (Chasles (Distance Oo M) C D).
	    rewrite H6.
	      rewrite <- H9.
	      rewrite (IsDistanceEqDistance C); trivial.
	    apply (SegmentTransBDC Oo).
	     apply (EquiOrientedClosedRaySegment Oo Uu).
	      trivial.
	      apply IsDistanceDistance.
	     apply (EquiOrientedClosedRaySegment Oo Uu).
	      rewrite <- (IsDistanceEqDistance C); trivial.
	      trivial.
	   apply (EquiOrientedClosedRaySegment Oo Uu).
	    trivial.
	    apply IsDistanceDistance.
	  apply (EquiOrientedTransCollinear (Distance Oo M) C).
	   apply CollinearBCA; apply SegmentCollinear.
	     apply (EquiOrientedClosedRaySegment Oo Uu).
	    rewrite <- (IsDistanceEqDistance C); trivial.
	    trivial.
	   trivial.
	   rewrite <- (IsDistanceEqDistance C); trivial.
Qed.

Lemma DistancePlusNeutralLeft : forall M : Point,
	DistancePlus Oo M = Distance Oo M.
Proof.
	intros; destructDistancePlus Oo ipattern:M ipattern:N.
	rewrite <- H; rewrite NullDistance.
	apply sym_eq; apply IsDistanceEqDistance.
	rewrite NullDistance in H0; immediate1.
Qed.

Lemma DistancePlusNeutralRight : forall M : Point,
	DistancePlus M Oo = Distance Oo M.
Proof.
	intros; rewrite DistancePlusCommut; apply DistancePlusNeutralLeft.
Qed.

Lemma DistancePlusNeutralRightEq : forall M N : Point,
	ClosedRay Oo Uu M ->
	ClosedRay Oo Uu N ->
	DistancePlus M N = M ->
	N = Oo.
Proof.
	intros.
	replace Oo with (Distance M (DistancePlus M N)).
	 apply sym_eq; apply IsDistancePlusEqDistance; immediate1.
	 rewrite H1; apply NullDistance.
Qed.

End SUM_OF_DISTANCES.
