Require Import A1_Plan A2_Orientation A4_Droite A5_Cercle A7_Tactics .
Require Import B2_CollinearProp .
Require Import C1_Distance C2_CircleAndDistance C7_Tactics .
Require Import D3_SecondDimension .
Require Import E4_Tactics.

Unset Standard Proposition Elimination Names.

Section INTERSECTION_DIAMETER_PROPERTIES.

Definition InterDiameterPoint (l : Line) (c : Circle) (H : Diameter l c) := 
let (M, _) := (InterDiameterPointDef l c H) in M.

Lemma EquiOrientedInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	EquiOriented (Center c) (InterDiameterPoint l c H) (LineA l) (LineB l).
Proof.
	intros; unfold InterDiameterPoint in |- *.
	setInterDiameter l c ipattern:(M).
	exact Heo.
Qed.

Lemma OnCircleInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	OnCircle c (InterDiameterPoint l c H).
Proof.
	intros; unfold InterDiameterPoint in |- *.
	setInterDiameter l c ipattern:(M).
	exact Hoc.
Qed.

Lemma OnLineInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	OnLine l (InterDiameterPoint l c H).
Proof.
	intros; unfold InterDiameterPoint in |- *.
	setInterDiameter l c ipattern:(M).
	destruct l; simplLine1.
	step4 Heo.
	simplCircle2.
	left; immediate4.
Qed.

Lemma EqDistanceInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	Distance (Center c) (InterDiameterPoint l c H) = Radius c.
Proof.
	intros; unfold InterDiameterPoint in |- *.
	setInterDiameter l c ipattern:(M).
	destruct c; simplCircle2.
	exact Hoc.
Qed.

Lemma UniqueInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c), forall M : Point,
	EquiOriented (Center c) M (LineA l) (LineB l) -> OnCircle c M ->
	M = InterDiameterPoint l c H.
Proof.
	intros; unfold InterDiameterPoint in |- *.
	setInterDiameter l c ipattern:(N).
	apply sym_eq; apply Hun; intuition.
Qed.

Lemma EqPointsInterDiameter :  forall (l : Line) (c : Circle) (H : Diameter l c), forall M N : Point,
	EquiOriented (Center c) M (LineA l) (LineB l) ->
	EquiOriented (Center c) N (LineA l) (LineB l) ->
	OnCircle c M ->
	OnCircle c N ->
	M = N.
Proof.
	intros.
	apply trans_eq with (y := InterDiameterPoint l c H).
	 apply UniqueInterDiameterPoint.
	  immediate4.
	  simpl in |- *; immediate4.
	 apply sym_eq; apply UniqueInterDiameterPoint.
	  immediate4.
	  simpl in |- *; immediate4.
Qed.

Definition SecondInterDiameterPoint (l : Line) (c : Circle) (H : Diameter l c) : Point.
Proof.
	destruct l; destruct c; unfold Diameter, OnLine; intros.
	exact  (InterDiameterPoint (Ruler B A (sym_not_eq n)) (Compass C A0 B0)  (CollinearBAC _ _ _ H)).
Defined.

Lemma EquiOrientedSecondInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	EquiOriented (Center c) (SecondInterDiameterPoint l c H) (LineB l) (LineA l).
Proof.
	destruct l; destruct c; unfold Diameter, OnLine in |- *; simpl in |- *;  intros.
	assert  (H0 :=  EquiOrientedInterDiameterPoint (Ruler B A (sym_not_eq n))   (Compass C A0 B0) (CollinearBAC A B C H)); simpl in H0.
	immediate4.
Qed.

Lemma OnCircleSecondInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	OnCircle c (SecondInterDiameterPoint l c H).
Proof.
	destruct l; destruct c; unfold Diameter, OnLine in |- *; simpl in |- *;  intros.
	change C with (Center (Compass C A0 B0)) in |- *.
	change (Distance A0 B0) with (Radius (Compass C A0 B0)) in |- *.
	apply EqDistanceInterDiameterPoint.
Qed.

Lemma OnLineSecondInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	OnLine l (SecondInterDiameterPoint l c H).
Proof.
	destruct l; destruct c; unfold Diameter, OnLine in |- *; simpl in |- *;  intros.
	assert (H0 := OnLineInterDiameterPoint (Ruler B A (sym_not_eq n))  (Compass C A0 B0) (CollinearBAC A B C H)); simpl in H0.
	immediate4.
Qed.

Lemma EqDistanceSecondInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c),
	Distance (Center c) (SecondInterDiameterPoint l c H) = Radius c.
Proof.
	destruct l; destruct c; unfold Diameter, OnLine in |- *; simpl in |- *;  intros.
	assert  (H0 := EqDistanceInterDiameterPoint (Ruler B A (sym_not_eq n))   (Compass C A0 B0) (CollinearBAC A B C H)); simpl in H0.
	immediate4.
Qed.

Lemma UniqueSecondInterDiameterPoint : forall (l : Line) (c : Circle) (H : Diameter l c), forall M : Point,
	EquiOriented (Center c) M (LineB l) (LineA l) -> OnCircle c M ->
	M = SecondInterDiameterPoint l c H.
Proof.
	destruct l; destruct c; unfold Diameter, OnLine in |- *; simpl in |- *; intros.
	apply UniqueInterDiameterPoint; immediate4.
Qed.

Lemma TwoDiameterInterPoints : forall l : Line, forall c : Circle, forall Hd : Diameter l c, forall M : Point,
	OnLine l M ->
	OnCircle c M ->
	M = InterDiameterPoint l c Hd \/ M =  SecondInterDiameterPoint l c Hd.
Proof.
	destruct l; destruct c; unfold Diameter, OnLine in |- *; simpl in |- *;  intros.
	destruct (TwoPointsOnLineOrientation C M (Ruler A B n)); simpl in *.
	 immediate2.
	 immediate2.
	 left; apply UniqueInterDiameterPoint; simpl in |- *.
	  immediate2.
	  immediate2.
	 right; apply UniqueInterDiameterPoint; simpl in |- *.
	  immediate2.
	  immediate2.
Qed.

End INTERSECTION_DIAMETER_PROPERTIES.

