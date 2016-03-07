Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A6_Intersection A7_Tactics.
Require Import B7_Tactics.

Section DISTANCE.

(* L'ensemble des distances est isomorphe a la demi-droite [OU). *)

Definition Distance (A B : Point) : Point.
Proof.
	setCircle0 Oo A B ipattern:(c).
	setInterDiameter1 lineOoUu c ipattern:(M).
	 immediate1.
	 exact M.
Defined.

Definition IsDistance (d : Point) := ClosedRay Oo Uu d.

Lemma DiameterlineOoUuuCircle :  Diameter lineOoUu uCircle.
Proof.
	simpl in |- *; immediate1.
Qed.

Ltac destructDistance A B AB := unfold Distance;
let H1 := fresh in (
	let H2 := fresh in (
		let H3 := fresh in (
			destruct (PointDef (fun M : Point =>
     				OnCircle1 (Compass Oo A B) M /\
     				EquiOriented (Center (Compass Oo A B)) M (LineA lineOoUu) (LineB lineOoUu)))
  			as (AB, ((H1, H2), H3))))).

Lemma EquiDistantSym : forall A B C D : Point,
	EquiDistant A B C D -> EquiDistant C D A B.
Proof.
	intros.
	apply (EquiDistantRec A B).
	 trivial.
	 apply EquiDistantRefl.
Qed.

Lemma IsDistanceDistance : forall A B : Point, IsDistance (Distance A B).
Proof.
	intros; destructDistance ipattern:(A) ipattern:(B) ipattern:(AB); simpl in *.
	unfold IsDistance in |- *; immediate1.
Qed.

Lemma EquiDistantDistance : forall A B : Point, EquiDistant Oo (Distance A B) A B.
Proof.
	intros; destructDistance ipattern:(A) ipattern:(B) ipattern:(AB); simpl in *.
	trivial.
Qed.

Lemma DistanceEq : forall A B C D : Point,
	EquiDistant A B C D -> Distance A B = Distance C D.
Proof.
	intros; destructDistance ipattern:(A) ipattern:(B) ipattern:(AB); destructDistance ipattern:(C) ipattern:(D) ipattern:(CD); simpl in *.
	apply H2; split.
	 apply (EquiDistantRec C D).
	  apply EquiDistantSym; trivial.
	  apply EquiDistantSym; trivial.
	 trivial.
Qed.

Lemma EqDistance : forall A B C D : Point,
	Distance A B = Distance C D -> EquiDistant A B C D.
Proof.
	intros; apply (EquiDistantRec Oo (Distance A B)).
	 apply EquiDistantDistance.
	 rewrite H; apply EquiDistantDistance.
Qed.

Lemma EqDistanceDistance : forall A B : Point, Distance Oo (Distance A B) = Distance A B.
Proof.
	intros; apply DistanceEq; apply EquiDistantDistance.
Qed.

Lemma NullDistance : forall A : Point, Distance A A = Oo.
Proof.
	intros; destructDistance ipattern:(A) ipattern:(A) ipattern:(AA); simpl in *.
	apply H1; split.
	 apply EquiDistantAABB.
	 immediate1.
Qed.

Lemma EqNullDistance : forall A B : Point, A = B -> Distance A B = Oo.
Proof.
	intros.
	rewrite H; apply NullDistance.
Qed.

Lemma DistinctEqDistanceDistinct : forall A B C D : Point,
	A <> B -> Distance A B = Distance C D -> C <> D.
Proof.
	intros.
	setLine0 A B ipattern:(ab).
	setCircle0 A C D ipattern:(g).
	setInterDiameter1 ab g ipattern:(E).
	 immediate1.
	 intro; elim H.
	   rewrite <- (Hun A).
	  apply Hun; split.
	   apply EqDistance; trivial.
	   immediate1.
	  split.
	   rewrite H1; apply EquiDistantAABB.
	   immediate1.
Qed.

Lemma DistanceEqDistanceDistinct : forall A B d : Point,
	d <> Oo -> Distance A B = d -> A <> B.
Proof.
	red in |- *; intros.
	subst; elim H.
	apply NullDistance.
Qed.

Lemma IsDistanceEqDistance : forall d : Point,
	IsDistance d ->
	Distance Oo d = d.
Proof.
	intros; destructDistance Oo ipattern:(d) ipattern:(dd).
	apply H2; split.
	 simpl in |- *; apply EquiDistantRefl.
	 unfold IsDistance in H; immediate1.
Qed.

Lemma DistanceNotNull : forall A B : Point,
	A <> B -> Distance A B <> Oo.
Proof.
	intros; apply sym_not_eq.
	apply (DistinctEqDistanceDistinct A B).
	trivial.
	rewrite EqDistanceDistance; trivial.
Qed.

Lemma NotNullDistance : forall A B : Point,
	Distance A B <> Oo -> A <> B.
Proof.
	red in |- *; intros; subst.
	elim H; apply NullDistance.
Qed.

Lemma DistanceSym : forall A B : Point,
	Distance A B = Distance B A.
Proof.
	intros; apply DistanceEq.
	apply EquiDistantABBA.
Qed.

Lemma EqDistanceTriangleSpec : forall A B C D E F A' B' C' D' E' F' : Point,
	TriangleSpec1 A B C D E F ->
	Distance A B = Distance A' B' ->
	Distance C D = Distance C' D' ->
	Distance E F = Distance E' F' ->
	TriangleSpec1 A' B' C' D' E' F'.
Proof.
	unfold TriangleSpec1 in |- *; intuition.
 	destruct H3 as (I, (J, (K, (L, (H6, (H7, (H8, (H9, H10)))))))).
 	  exists I; exists J; exists K; exists L; intuition.
 	 apply EqDistance; rewrite <- H0; apply DistanceEq; trivial.
 	 apply EqDistance; rewrite <- H1; apply DistanceEq; trivial.
 	 apply EqDistance; rewrite <- H2; apply DistanceEq; trivial.
 	destruct H as (I, (J, (K, (L, (H6, (H7, (H8, (H9, H10)))))))).
 	  exists I; exists J; exists K; exists L; intuition.
 	 apply EqDistance; rewrite <- H1; apply DistanceEq; trivial.
 	 apply EqDistance; rewrite <- H2; apply DistanceEq; trivial.
 	 apply EqDistance; rewrite <- H0; apply DistanceEq; trivial.
 	destruct H5 as (I, (J, (K, (L, (H6, (H7, (H8, (H9, H10)))))))).
 	  exists I; exists J; exists K; exists L; intuition.
 	 apply EqDistance; rewrite <- H2; apply DistanceEq; trivial.
 	 apply EqDistance; rewrite <- H0; apply DistanceEq; trivial.	
 	 apply EqDistance; rewrite <- H1; apply DistanceEq; trivial.
Qed.

Lemma UnitDistance : Distance Oo Uu = Uu.
Proof.
	apply IsDistanceEqDistance.
	unfold IsDistance in |- *; immediate1.
Qed.

End DISTANCE.
