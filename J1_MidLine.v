Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import B1_ClockwiseProp B7_Tactics .
Require Import C1_Distance .
Require Import D2_ExistsClockwise .
Require Import G1_Angles .
Require Import H1_Triangles H2_ParticularTriangles H4_Tactics .
Require Import I4_Tactics.

Section MIDLINE.

Definition MidLine (A B : Point) : A <> B -> Line.
Proof.
	intros.
	setEquilateral7 A B ipattern:C.
	setEquilateral7 B A ipattern:D.
	setLine0 C D ipattern:m.
	 step8 H0.
	 exact m.
Defined.

Ltac destructMidLine A B H :=
let m := fresh "m" in (
	pose (m := MidLine A B H); fold m in |- *;
	unfold MidLine in m;
	let C := fresh "C" in (
		setEquilateral7 A B C; fold C in m;
		let D := fresh "D" in (
			setEquilateral7 B A D; fold D in m;
			let Hyp := fresh in (
				pose (Hyp := FigureDistinct  (fun M : Point => Clockwise B A M) C D
    						(ClockwiseCAB A C B (ClockwiseExistsClockwise A B H))
   						(ClockwiseNotClockwise A B D
       							(ClockwiseCAB B D A (ClockwiseExistsClockwise B A (sym_not_eq H))))); fold Hyp in m)))).

Lemma EquilateralAMidLineAB : forall A B : Point, forall H : A <> B,
	Equilateral (Tr A (LineA (MidLine A B H)) B).
Proof.
	intros; destructMidLine ipattern:A ipattern:B ipattern:H.
	 immediate8.
Qed.

Lemma EquilateralBMidLineBA : forall A B : Point, forall H : A <> B,
	Equilateral (Tr B (LineB (MidLine A B H)) A).
Proof.
	intros; destructMidLine ipattern:A ipattern:B ipattern:H.
	 immediate8.
Qed.

Lemma ClockwiseAMidLineAB : forall A B : Point, forall H : A <> B,
	Clockwise  A (LineA (MidLine A B H)) B.
Proof.
	intros; destructMidLine ipattern:A ipattern:B ipattern:H.
	 immediate8.
Qed.

Lemma ClockwiseBMidLineBA : forall A B : Point, forall H : A <> B,
	Clockwise B (LineB (MidLine A B H)) A.
Proof.
	intros; destructMidLine ipattern:A ipattern:B ipattern:H.
	 immediate8.
Qed.

Lemma TCongruentMidLineAMidLineB : forall A B : Point, forall H : A <> B,
TCongruent (Tr (LineA (MidLine A B H)) (LineB (MidLine A B H)) A) (Tr (LineA (MidLine A B H)) (LineB (MidLine A B H)) B).
Proof.
	intros; destructMidLine ipattern:A ipattern:B ipattern:H.
	simplLine1.
	step8 1; immediate8.
Qed.

Lemma OnMidLineEqDistance : forall A B : Point, forall H : A <> B,
forall M : Point, OnLine (MidLine A B H) M ->
	Distance M A = Distance M B.
Proof.
	intros A B H.
	generalize (TCongruentMidLineAMidLineB A B H).
	destructMidLine A B H.
	simplLine1; intros.
	by2Cases1 H4.
	 from8 4 (TCongruent (Tr M A C) (Tr M B C)).
	  step8 H3.
	  from8 H5 (CongruentAngle A C M A C D).
	    step8 H6.
	    step8 H3.
	 from8 4 (TCongruent (Tr M A D) (Tr M B D)).
	  step8 H3.
	  from8 H5 (CongruentAngle A D M A D C).
	    step8 H6.
	    from8 H3 (CongruentAngle A D C B D C).
	    step8 H7.
Qed.

End MIDLINE.
