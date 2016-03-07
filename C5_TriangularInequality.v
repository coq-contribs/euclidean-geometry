Require Import A1_Plan A2_Orientation A3_Metrique A5_Cercle A7_Tactics .
Require Import B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe.

Section TRIANGULAR_INEQUALITY.

Definition TriangularInequality (A B C D E F : Point) := DistanceLe (Distance E F) (DistancePlus (Distance A B) (Distance C D)).

Definition TriangleSpec := fun A B C D E F : Point =>
	TriangularInequality A B C D E F /\ TriangularInequality C D E F A B /\ TriangularInequality E F A B C D.

Definition SecantCircles (c1 c2 : Circle) := 
	Center c1 <> Center c2 /\
	TriangleSpec (RadiusA c1) (RadiusB c1) (RadiusA c2) (RadiusB c2) (Center c1) (Center c2).

Lemma TriangularInequalityTriangleInequality : forall A B C D E F : Point,
	TriangularInequality A B C D E F -> TriangleInequality A B C D E F.
Proof.
	unfold TriangularInequality, TriangleInequality in |- *; intros.
	exists Oo; exists (Distance A B); exists (DistancePlus (Distance A B) (Distance C D));  exists (Distance E F); intuition.
	 apply IsDistanceSegmentDistancePlus.
	   apply IsDistanceDistance.
	 apply EquiDistantSym; apply EquiDistantDistance.
	 apply EqDistance; rewrite IsDistancePlusEqDistance.
	  trivial.
	  apply IsDistanceDistance.
	  apply IsDistanceDistance.
	 apply EquiDistantSym; apply EquiDistantDistance.
Qed.

Lemma TriangleInequalityTriangularInequality : forall A B C D E F : Point,
	TriangleInequality A B C D E F -> TriangularInequality A B C D E F.
Proof.
	unfold TriangularInequality, TriangleInequality in |- *;
	 intros A B C D E F (G, (H, (I, (J, (H0, (H1, (H2, (H3, H4)))))))).
	generalize (DistanceEq _ _ _ _ H1); generalize (DistanceEq _ _ _ _ H2);
	 generalize (DistanceEq _ _ _ _ H4); clear H1 H2 H4; 
	 intros H4 H2 H1.
	rewrite H4; rewrite H2; rewrite H1.
	rewrite Chasles.
	 apply SegmentDistanceLe.
	   trivial.
	 trivial.
Qed.

Lemma TriangularInequalityABBCAC : forall A B C : Point,
	TriangularInequality A B B C A C.
Proof.
	unfold TriangularInequality in |- *; intros.
	apply (EquiDistantTriangle A B C Oo (Distance A B)  (DistancePlus (Distance A B) (Distance B C)) (Distance A C) Uu).
	 apply IsDistanceSegmentDistancePlus; apply IsDistanceDistance.
	 immediate1.
	 apply IsDistanceDistancePlus.
	 apply IsDistanceDistance.
	 apply EquiDistantSym; apply EquiDistantDistance.
	 apply EqDistance; apply sym_eq.
	   apply IsDistancePlusEqDistance; apply IsDistanceDistance.
	 apply EquiDistantSym; apply EquiDistantDistance.
Qed.

Lemma TriangularInequalityABBCCA : forall A B C : Point,
	TriangularInequality A B B C C A.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym C A).
	    apply TriangularInequalityABBCAC.
Qed.

Lemma TriangularInequalityABCBAC : forall A B C : Point,
	TriangularInequality A B C B A C.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym C B).
	    apply TriangularInequalityABBCAC.
Qed.

Lemma TriangularInequalityABCBCA : forall A B C : Point,
	TriangularInequality A B C B C A.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym C B).
	    apply TriangularInequalityABBCCA.
Qed.

Lemma TriangularInequalityBABCAC : forall A B C : Point,
	TriangularInequality B A B C A C.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym B A).
	    apply TriangularInequalityABBCAC.
Qed.

Lemma TriangularInequalityBABCCA : forall A B C : Point,
	TriangularInequality B A B C C A.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym B A).
	    apply TriangularInequalityABBCCA.
Qed.

Lemma TriangularInequalityBACBAC : forall A B C : Point,
	TriangularInequality B A C B A C.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym B A).
	    apply TriangularInequalityABCBAC.
Qed.

Lemma TriangularInequalityBACBCA : forall A B C : Point,
	TriangularInequality B A C B C A.
Proof.
	unfold TriangularInequality in |- *; intros.
	   rewrite (DistanceSym B A).
	    apply TriangularInequalityABCBCA.
Qed.

Lemma TriangleSpecSpec1 : forall A B C D E F : Point,
	TriangleSpec A B C D E F -> TriangleSpec1 A B C D E F.
Proof.
	unfold TriangleSpec, TriangleSpec1 in |- *; intuition.
	 apply TriangularInequalityTriangleInequality; trivial.
	 apply TriangularInequalityTriangleInequality; trivial.
	 apply TriangularInequalityTriangleInequality; trivial.
Qed.

Lemma TriangleSpec1Spec : forall A B C D E F : Point,
	TriangleSpec1 A B C D E F -> TriangleSpec A B C D E F.
Proof.
	unfold TriangleSpec, TriangleSpec1 in |- *; intuition.
	 apply TriangleInequalityTriangularInequality; trivial.
	 apply TriangleInequalityTriangularInequality; trivial.
	 apply TriangleInequalityTriangularInequality; trivial.
Qed.

Lemma TriangleSpecABBCAC : forall A B C : Point,
	TriangleSpec A B B C A C.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityABBCAC.
	 apply TriangularInequalityABCBCA.
	 apply TriangularInequalityBABCCA.
Qed.

Lemma TriangleSpecABBCCA : forall A B C : Point,
	TriangleSpec A B B C C A.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityABBCCA.
	 apply TriangularInequalityABBCCA.
	 apply TriangularInequalityABBCCA.
Qed.

Lemma TriangleSpecABCBAC : forall A B C : Point,
	TriangleSpec A B C B A C.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityABCBAC.
	 apply TriangularInequalityBACBCA.
	 apply TriangularInequalityBABCAC.
Qed.

Lemma TriangleSpecABCBCA : forall A B C : Point,
	TriangleSpec A B C B C A.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityABCBCA.
	 apply TriangularInequalityBABCCA.
	 apply TriangularInequalityABBCAC.
Qed.

Lemma TriangleSpecBABCAC : forall A B C : Point,
	TriangleSpec B A B C A C.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityBABCAC.
	 apply TriangularInequalityABCBAC.
	 apply TriangularInequalityBACBCA.
Qed.

Lemma TriangleSpecBABCCA : forall A B C : Point,
	TriangleSpec B A B C C A.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityBABCCA.
	 apply TriangularInequalityABBCAC.
	 apply TriangularInequalityABCBCA.
Qed.

Lemma TriangleSpecBACBAC : forall A B C : Point,
	TriangleSpec B A C B A C.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityBACBAC.
	 apply TriangularInequalityBACBAC.
	 apply TriangularInequalityBACBAC.
Qed.

Lemma TriangleSpecBACBCA : forall A B C : Point,
	TriangleSpec B A C B C A.
Proof.
	unfold TriangleSpec in |- *; intuition.
	 apply TriangularInequalityBACBCA.
	 apply TriangularInequalityBABCAC.
	 apply TriangularInequalityABCBAC.
Qed.

Lemma TriangleSpecEq : forall A B C D E F AA BB CC DD EE FF: Point,
	TriangleSpec A B C D E F -> 
	Distance A B = Distance AA BB ->
	Distance C D = Distance CC DD ->
	Distance E  F = Distance EE FF ->
	TriangleSpec AA BB CC DD EE FF .
Proof.
	unfold TriangleSpec, TriangularInequality in |- *; intros.
	rewrite <- H0; rewrite <- H1; rewrite <- H2; intuition.
Qed.

Lemma SecantCirclesSym : forall c1 c2 : Circle, 
	SecantCircles c1 c2 -> SecantCircles c2 c1.
Proof.
	unfold SecantCircles, TriangleSpec, TriangularInequality in |- *; destruct c1; destruct c2; simpl in |- *; intuition.
	 rewrite (DistanceSym C0 C); rewrite DistancePlusCommut; trivial.
	 rewrite (DistanceSym C0 C); rewrite DistancePlusCommut; trivial.
	 rewrite (DistanceSym C0 C); rewrite DistancePlusCommut; trivial.
Qed.

Lemma InterCirclesPointDef : forall c1 c2 : Circle,
	SecantCircles c1 c2 ->
	let f := (fun M : Point => OnCircle c1 M /\ OnCircle c2 M /\ ~Clockwise (Center c2) M (Center c1)) in
	{M : Point |  f M /\ Unicity M f}.
Proof.
	intros.
	setInterCircles1 c1 c2 ipattern:(P).
	 unfold SecantCircles, SecantCircles1 in *; intuition.
	   apply TriangleSpecSpec1; trivial.
	 exists P; unfold f in |- *; simpl in |- *; intuition.
	  apply OnCircle1OnCircle; trivial.
	  apply OnCircle1OnCircle; trivial.
	  unfold Unicity in *; intuition.
	    apply Hun; intuition.
	   apply OnCircleOnCircle1; trivial.
	   apply OnCircleOnCircle1; trivial.
Qed.

End TRIANGULAR_INEQUALITY.
