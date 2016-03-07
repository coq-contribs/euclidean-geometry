Require Import A1_Plan A2_Orientation A5_Cercle A7_Tactics .
Require Import B7_Tactics .
Require Import C1_Distance C5_TriangularInequality C7_Tactics.

Section BUILDING_CLOCKWISE.

Lemma  EquilateralInequality : forall A B : Point, 
	TriangularInequality A B A B A B.
Proof.
	unfold TriangularInequality in |- *; intros.
	immediate2.
Qed.

Lemma EquilateralTriangleSpec : forall A B : Point, 
	TriangleSpec A B A B A B.
Proof.
	intros; unfold TriangleSpec in |- *.
	assert (H := EquilateralInequality A B); intuition.
Qed.

Definition ExistsClockwise (A B : Point) : A <> B -> Point.
Proof.
	intros.
	setCircle0 A A B ipattern:(gamma1).
	setCircle0 B A B ipattern:(gamma2).
	setInterCircles gamma1 gamma2 ipattern:(C).
	  exact (EquilateralTriangleSpec A B).
	 exact C.
Defined.

Ltac destructExistsClockwise A B H := unfold ExistsClockwise in |- *;
	destruct (InterCirclesPointDef (Compass A A B) (Compass B A B)) as (C, ((H1, (H2, H3)), H4)); simpl in *.

Lemma NotOpenRayABExistsClockwise : forall (A B : Point) (H : A <> B),
	~OpenRay A B (ExistsClockwise A B H).
Proof.
	intros; destructExistsClockwise ipattern:(A) ipattern:(B) ipattern:(H).
	setLine0 A B ipattern:(ab).
	setCircle0 A A B ipattern:(g).
	setInterDiameter ab g ipattern:(D).
	 intro; elim (DistinctEqDistanceDistinct A B B C H (sym_eq H2)).
	   apply trans_eq with (y := D).
	  apply sym_eq; apply Hun; split; immediate2.
	  apply Hun; split; immediate2.
Qed.

Lemma NotOpenRayBAExistsClockwise : forall (A B : Point) (H : A <> B),
	~OpenRay B A (ExistsClockwise A B H).
Proof.
	intros; destructExistsClockwise ipattern:(A) ipattern:(B) ipattern:(H).
	setLine0 B A ipattern:(ba).
	setCircle0 B A B ipattern:(g).
	setInterDiameter ba g ipattern:(D).
	 intro; elim (DistinctEqDistanceDistinct A B A C H (sym_eq H1)).
	   apply trans_eq with (y := D).
	  apply sym_eq; apply Hun; split; immediate2.
	  apply Hun; split; immediate2.
Qed.

Lemma NotClockwiseExistsClockwise : forall (A B : Point) (H : A <> B),
	~Clockwise A B (ExistsClockwise A B H).
Proof.
	intros; destructExistsClockwise ipattern:(A) ipattern:(B) ipattern:(H).
	intro; elim H3; immediate2.
Qed.

Lemma ClockwiseExistsClockwise : forall (A B : Point) (H : A <> B),
	Clockwise A (ExistsClockwise A B H) B.
Proof.
	intros; by4Cases1 ipattern:(A) ipattern:(B) (ExistsClockwise A B H).
	 elim (NotClockwiseExistsClockwise A B H); immediate2.
	 immediate2.
	 elim (NotOpenRayABExistsClockwise A B H); immediate2.
	 elim (NotOpenRayBAExistsClockwise A B H); immediate2.
Qed.

End BUILDING_CLOCKWISE.
