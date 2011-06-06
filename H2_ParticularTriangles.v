Section PARTICULAR_TRIANGLES.

(* non degenerated *)

Definition TStrict (t : Triangle) := match t with (Tr A B C) => Clockwise A B C \/ Clockwise A C B end.

Lemma TCongruentTStrict : forall t1 t2 : Triangle,
	TCongruent t1 t2 -> TStrict t1 -> TStrict t2.
Proof.
	destruct t1; destruct t2; unfold TCongruent in |- *; intuition.
	by3Cases1 p2 p3 p4; intuition.
	 left; immediate6.
	 right; immediate6.
	 by3SegmentCases1 H4.
	  since6 (Segment p p0 p1).
	   apply ChaslesRec.
	     step6 H3; step6 H.
	     usingChasles2 p2 p4 p3.
	   destruct H0.
	    contradict1 H0 H5.
	    contradict1 H0 H5.
	  since6 (Segment p0 p1 p).
	   apply ChaslesRec.
	     step6 H1; step6 H3.
	     usingChasles2 p3 p2 p4.
	   destruct H0.
	    contradict1 H0 H5.
	    contradict1 H0 H5.
	  since6 (Segment p1 p p0).
	   apply ChaslesRec.
	     step6 H; step6 H1.
	     usingChasles2 p2 p3 p4.
	   destruct H0.
	    contradict1 H0 H5.
	    contradict1 H0 H5.
Qed.

Lemma TStrictDistinctAB : forall A B C : Point, TStrict (Tr A B C) -> A <> B.
Proof.
	intros; destruct H; immediate6.
Qed.

Lemma TStrictDistinctBC : forall A B C : Point, TStrict (Tr A B C) -> B <> C.
Proof.
	intros; destruct H; immediate6.
Qed.

Lemma TStrictDistinctCA : forall A B C : Point, TStrict (Tr A B C) -> C <> A.
Proof.
	intros; destruct H; immediate6.
Qed.

(* isoceles *)

Definition Isosceles1 (t : Triangle) := match t with (Tr A B C) => Distance A B = Distance A C end.

Definition Isosceles2 (t : Triangle) :=  match t with (Tr A B C) => Distance B C = Distance B A end.

Definition Isosceles3 (t : Triangle) :=  match t with (Tr A B C) => Distance C A = Distance C B end.

Lemma Isosceles1Sym : forall A B C : Point,
	Isosceles1 (Tr  A B C) -> Isosceles1 (Tr  A C B).
Proof.
	intros; simpl in *; immediate6.
Qed.

Lemma Isosceles2Sym : forall A B C : Point,
	Isosceles2 (Tr  A B C) -> Isosceles2 (Tr  C B A).
Proof.
	intros; simpl in *; immediate6.
Qed.

Lemma Isosceles3Sym : forall A B C : Point,
	Isosceles3 (Tr  A B C) -> Isosceles3 (Tr  B A C).
Proof.
	intros; simpl in *; immediate6.
Qed.

Lemma Isosceles12 : forall A B C : Point,
	Isosceles1 (Tr  A B C) -> Isosceles2 (Tr  C A B).
Proof.
	intros; simpl in *; immediate6.
Qed.

Lemma Isosceles23 : forall A B C : Point,
	Isosceles2 (Tr  A B C) -> Isosceles3 (Tr  C A B).
Proof.
	intros; simpl in *; immediate6.
Qed.

Lemma Isosceles31 : forall A B C : Point,
	Isosceles3 (Tr  A B C) -> Isosceles1 (Tr  C A B).
Proof.
	intros; simpl in *; immediate6.
Qed.

Lemma IsoscelesEqAngles1 : forall A B C : Point,
	B <> A ->
	B <> C ->
	C <> A ->
	Isosceles1 (Tr A B C) ->
	CongruentAngle A B C A C B.
Proof.
	intros.
	apply TCongruentAnglesB.
	 immediate6.
	 immediate6.
	 immediate6.
	 immediate6.
	simpl in H2; apply SSSTCongruent; immediate6.
Qed.

Lemma IsoscelesEqAngles2 : forall A B C : Point,
	 C <> B ->
	 C <> A ->
	A <> B ->
	Isosceles2 (Tr A B C) ->
	CongruentAngle B C A B A C.
Proof.
	intros.
	apply TCongruentAnglesB.
	 immediate6.
	 immediate6.
	 immediate6.
	 immediate6.
	simpl in H2; apply SSSTCongruent; immediate6.
Qed.

Lemma IsoscelesEqAngles3 : forall A B C : Point,
	A <> C ->
	A <> B ->
	B <> C ->
	Isosceles3 (Tr A B C) ->
	CongruentAngle C A B C B A.
Proof.
	intros.
	apply TCongruentAnglesB.
	 immediate6.
	 immediate6.
	 immediate6.
	 immediate6.
	simpl in H2; apply SSSTCongruent; immediate6.
Qed.

Lemma EqAnglesIsosceles1 : forall A B C : Point,
	~Collinear A B C ->
	CongruentAngle A B C A C B ->
	Isosceles1 (Tr A B C).
Proof.
	intros; simpl in |- *.
	apply (TCongruentEqSidesBC C A B B A C).
	apply (ASATCongruent C A B B A C).
	 immediate6.
	 step6 H0.
	 immediate6.
	 immediate6.
Qed.

Lemma EqAnglesIsosceles2 : forall A B C : Point,
	~Collinear A B C ->
	CongruentAngle B C A B A C ->
	Isosceles2 (Tr A B C).
Proof.
	intros; simpl in |- *.
	apply (TCongruentEqSidesBC A B C C B A).
	apply (ASATCongruent A B C C B A).
	 immediate6.
	 step6 H0.
	 immediate6.
	 immediate6.
Qed.

Lemma EqAnglesIsosceles3 : forall A B C : Point,
	~Collinear A B C ->
	CongruentAngle C A B C B A ->
	Isosceles3 (Tr A B C).
Proof.
	intros; simpl in |- *.
	apply (TCongruentEqSidesBC B C A A C B).
	apply (ASATCongruent B C A A C B).
	 immediate6.
	 step6 H0.
	 immediate6.
	 immediate6.
Qed.

(* equilateral *)

Definition Equilateral (t : Triangle) :=  
	match t with (Tr A B C) => Distance A B = Distance A C /\  Distance A B = Distance B C end.

Lemma EquilateralSym : forall A B C : Point,
	Equilateral (Tr  A B C) -> Equilateral (Tr  A C B).
Proof.
	intros; simpl in *.
	intuition.
	step6 H0.
Qed.

Lemma EquilateralPerm : forall A B C : Point,
	Equilateral (Tr  A B C) -> Equilateral (Tr  B C A).
Proof.
	intros; simpl in *.
	intuition.
	 immediate6.
	 step6 H0.
Qed.

Lemma Isosceles12Equilateral : forall A B C : Point,
	Isosceles1 (Tr  A B C) -> 
	Isosceles2 (Tr  A B C) -> 
	Equilateral (Tr  A B C).
Proof.
	intros; simpl in *.
	intuition.
	 immediate6.
Qed.

Lemma Isosceles23Equilateral : forall A B C : Point,
	Isosceles2 (Tr  A B C) -> 
	Isosceles3 (Tr  A B C) -> 
	Equilateral (Tr  A B C).
Proof.
	intros; simpl in *.
	intuition.
	 step6 H0.
	 immediate6.
Qed.

Lemma Isosceles31Equilateral : forall A B C : Point,
	Isosceles3 (Tr  A B C) -> 
	Isosceles1 (Tr  A B C) -> 
	Equilateral (Tr  A B C).
Proof.
	intros; simpl in *.
	intuition.
	 step6 H0.
Qed.

Lemma EquilateralIsosceles1 : forall A B C : Point,
	Equilateral (Tr  A B C) -> 
	Isosceles1 (Tr  A B C).
Proof.
	intros; simpl in *.
	intuition.
Qed.

Lemma EquilateralIsosceles2 : forall A B C : Point,
	Equilateral (Tr  A B C) -> 
	Isosceles2 (Tr  A B C).
Proof.
	intros; simpl in *.
	intuition.
	 immediate6.
Qed.

Lemma EquilateralIsosceles3 : forall A B C : Point,
	Equilateral (Tr  A B C) -> 
	Isosceles3 (Tr  A B C).
Proof.
	intros; simpl in *.
	intuition.
	step6 H1.
Qed.

Lemma EquilateralEqSides12 : forall A B C : Point,
	Equilateral (Tr  A B C) -> 
	Distance A B = Distance A C.
Proof.
	intros; simpl in *.
	intuition.
Qed.

Lemma EquilateralEqSides23 : forall A B C : Point,
	Equilateral (Tr  A B C) -> 
	Distance B C = Distance B A.
Proof.
	intros; simpl in *.
	intuition.
	 immediate6.
Qed.

Lemma EquilateralEqSides31 : forall A B C : Point,
	Equilateral (Tr  A B C) -> 
	Distance C A = Distance C B.
Proof.
	intros; simpl in *.
	intuition.
	 immediate6.
Qed.

Lemma EquilateralExistsClockwise : forall A B : Point, forall (H : A <> B), 
	Equilateral (Tr A (ExistsClockwise A B H) B).
Proof.
	intros.
	unfold ExistsClockwise in |- *.
	destruct (InterCirclesPointDef (Compass A A B) (Compass B A B)) as (D, ((H0, (H1, H2)), H3)).
	simpl in |- *; intuition.
	 step6 H0.
Qed.

End PARTICULAR_TRIANGLES.
