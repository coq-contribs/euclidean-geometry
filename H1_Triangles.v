Require Import A1_Plan A2_Orientation A7_Tactics .
Require Import B7_Tactics .
Require Import C1_Distance C5_TriangularInequality C7_Tactics .
Require Import D5_Tactics .
Require Import F5_Tactics .
Require Import G1_Angles G4_Tactics.

Section TRIANGLES.

Inductive Triangle : Set :=
	| Tr : Point -> Point -> Point -> Triangle.

Definition TCongruent (t1 t2 : Triangle) := 
	match t1 with (Tr A1 B1 C1) =>
	match t2 with (Tr A2 B2 C2) =>
	Distance A1 B1 = Distance A2 B2 /\ Distance B1 C1 = Distance B2 C2 /\ Distance C1 A1 = Distance C2 A2
end end.

Lemma TCongruentSym : forall t1 t2 : Triangle,
	TCongruent t1 t2 -> TCongruent t2 t1.
Proof.
	intros; destruct t1; destruct t2; simpl in *.
	intuition; immediate6.
Qed.

Lemma TCongruentTrans : forall t1 t2 t3: Triangle,
	TCongruent t1 t2 -> TCongruent t2 t3 -> TCongruent t1 t3.
Proof.
	intros; destruct t1; destruct t2; destruct t3; simpl in *.
	intuition.
	 step5 H1.
	 step5 H0.
	 step5 H4.
Qed.

Lemma TCongruentPerm : forall A1 B1 C1 A2 B2 C2 : Point,
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	TCongruent (Tr B1 C1 A1) (Tr B2 C2 A2).
Proof.
	simpl in |- *; intuition.
Qed.

Lemma TCongruentSubst : forall A1 B1 C1 A2 B2 C2 : Point,
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	TCongruent (Tr B1 A1 C1) (Tr B2 A2 C2).
Proof.
	simpl in |- *; intuition; immediate6.
Qed.

Lemma SSSTCongruent : forall A1 B1 C1 A2 B2 C2 : Point,
	Distance A1 B1 = Distance A2 B2 ->
	Distance B1 C1 = Distance B2 C2 ->
	Distance C1 A1 = Distance C2 A2 ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2).
Proof.
	simpl in |- *; intuition.
Qed.

Lemma TCongruentEqSidesAB : forall A1 B1 C1 A2 B2 C2 : Point,
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	Distance A1 B1 = Distance A2 B2.
Proof.
	simpl in |- *; intuition.
Qed.

Lemma TCongruentEqSidesBC : forall A1 B1 C1 A2 B2 C2 : Point,
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	Distance B1 C1 = Distance B2 C2.
Proof.
	simpl in |- *; intuition.
Qed.

Lemma TCongruentEqSidesCA : forall A1 B1 C1 A2 B2 C2 : Point,
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	Distance C1 A1 = Distance C2 A2.
Proof.
	simpl in |- *; intuition.
Qed.

Lemma TCongruentAnglesA : forall A1 B1 C1 A2 B2 C2 : Point, 
	A1 <> C1 ->
	A1 <> B1 ->
	A2 <> C2 ->
	A2 <> B2 ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	CongruentAngle C1 A1 B1 C2 A2 B2.
Proof.
	simpl in |- *; intros.
	apply CongruentSSS; intuition; immediate6.
Qed.

Lemma TCongruentAnglesB : forall A1 B1 C1 A2 B2 C2 : Point, 
	B1 <> A1 ->
	B1 <> C1 ->
	B2 <> A2 ->
	B2 <> C2 ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	CongruentAngle A1 B1 C1 A2 B2 C2.
Proof.
	simpl in |- *; intros.
	apply CongruentSSS; intuition; immediate6.
Qed.

Lemma TCongruentAnglesC : forall A1 B1 C1 A2 B2 C2 : Point,
	C1 <> B1 ->
	C1 <> A1 ->
	C2 <> B2 ->
	 C2 <> A2 ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2) ->
	CongruentAngle B1 C1 A1 B2 C2 A2.
Proof.
	simpl in |- *; intros.
	apply CongruentSSS; intuition; immediate6.
Qed.

Lemma SASTCongruent : forall A1 B1 C1 A2 B2 C2 : Point, 
	Distance A1 B1 = Distance A2 B2 ->
	Distance B1 C1 = Distance B2 C2 ->
	CongruentAngle A1 B1 C1 A2 B2 C2   ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2).
Proof.
	simpl in |- *; intuition.
	rewrite (DistanceSym C1 A1); rewrite (DistanceSym C2 A2); apply (CongruentSAS B1 A1 C1 B2 A2 C2); immediate6.
Qed.

Lemma ASATClockwiseCongruent : forall A1 B1 C1 A2 B2 C2 : Point, 
	Clockwise A1 B1 C1 ->
	CongruentAngle C1 A1 B1 C2 A2 B2  ->
	CongruentAngle B1 C1 A1 B2 C2 A2  ->
	Distance C1 A1 = Distance C2 A2 ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2).
Proof.
	intros.
	setCircle0 A1 A2 B2 ipattern:(gamma1).
	setCircle0 C1 C2 B2 ipattern:(gamma2).
	setIntersectionCircles3 gamma1 gamma2 ipattern:(B3).
	 since6 (TriangleSpec A2 B2 C2 B2 A2 C2).
	  simplCircle2; step6 H3.
	 since6 (TCongruent (Tr A1 B3 C1) (Tr A2 B2 C2)).
	  apply SSSTCongruent; immediate6.
	  assert (Ha1b3 : A1 <> B3).
	   step6 H4; immediate6.
	   from6 H0 (CongruentAngle C1 A1 B1 C1 A1 B3).
	      apply TCongruentAnglesA.
	     immediate6.
	     immediate6.
	     immediate6.
	     immediate6.
	     apply TCongruentSym; exact H7.
	    from6 H1 (CongruentAngle B1 C1 A1 B3 C1 A1).
	       apply TCongruentAnglesC.
	      immediate6.
	      immediate6.
	      step6 H5; immediate6.
	      immediate6.
	      apply TCongruentSym; exact H7.
	     from6 H9 (OpenRay C1 B1 B3).
	      from6 H8 (OpenRay A1 B1 B3).
	       from6 H (B1 = B3).
	        subst; immediate6.
Qed.

Lemma ASATCongruent : forall A1 B1 C1 A2 B2 C2 : Point, 
	~Collinear A1 B1 C1 ->
	CongruentAngle C1 A1 B1 C2 A2 B2  ->
	CongruentAngle B1 C1 A1 B2 C2 A2  ->
	Distance C1 A1 = Distance C2 A2 ->
	TCongruent (Tr A1 B1 C1) (Tr A2 B2 C2).
Proof.
	intros.
	by2Cases1 H.
	 apply (ASATClockwiseCongruent A1 B1 C1 A2 B2 C2); immediate6.
	 apply TCongruentSubst; apply TCongruentPerm.
	   apply (ASATClockwiseCongruent C1 B1 A1 C2 B2 A2); immediate6.
Qed.

End TRIANGLES.
