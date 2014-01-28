Require Import A1_Plan A2_Orientation A4_Droite A5_Cercle A7_Tactics .
Require Import D3_SecondDimension .
Require Import L6_Tactics.

Section EQUAL_LINES.

Inductive EqLine : Line -> Line -> Prop :=
	| EqLineDef : forall d1 d2 : Line, OnLine d1 (LineA d2) -> OnLine d1 (LineB d2) -> EqLine d1 d2. 

Lemma OnLineDistinct : forall A B : Point, forall d : Line,
	OnLine d A ->
	~OnLine d B ->
	A <> B.
Proof.
	intros.
	contrapose0 H0.
	rewrite <- H0; immediate11.
Qed.

Lemma EqLineOnLine : forall d1 d2 : Line, forall M : Point,
	EqLine d1 d2 ->
	OnLine d1 M ->
	OnLine d2 M.
Proof.
	intros.
	inversion H.
	destruct d2; simpl in |- *.
	step11 d1.
Qed.

Lemma OnLineEqLine : forall d1 d2 : Line, 
	(forall M : Point, OnLine d2 M -> OnLine d1 M) ->
	EqLine d1 d2.
Proof.
	intros; constructor.
	 apply H; immediate11.
	 apply H; immediate11.
Qed.

Lemma EqLineRefl : forall d : Line, EqLine d d.
Proof.
	destruct d; intros; constructor; immediate11.
Qed.

Lemma EqLineSym : forall d1 d2 : Line, EqLine d1 d2 -> EqLine d2 d1.
Proof.
	intros.
	apply OnLineEqLine; intros.
	apply (EqLineOnLine d1 d2); immediate11.
Qed.

Lemma EqLineTrans : forall d1 d2 d3 : Line, EqLine d1 d2 -> EqLine d2 d3 -> EqLine d1 d3.
Proof.
	intros.
	apply EqLineSym.
	apply OnLineEqLine; intros.
	apply (EqLineOnLine d2 d3 M H0).
	apply (EqLineOnLine d1 d2); immediate11.
Qed.

Lemma EqLineId : forall A B : Point, forall H1 H2 : A <> B,
	EqLine (Ruler A B H1) (Ruler A B H2).
Proof.
	intros; constructor; immediate11.
Qed.

Lemma EqLineOpp : forall A B : Point, forall H1 : A <> B, forall H2 : B <> A,
	EqLine (Ruler A B H1) (Ruler B A H2).
Proof.
	intros; constructor; immediate11.
Qed.

Lemma EqLineDiameter : forall d1 d2 : Line, forall c : Circle,
	EqLine d1 d2 -> Diameter d1 c -> Diameter d2 c.
Proof.
	unfold Diameter in |- *; intros.
	apply (EqLineOnLine d1 d2 (Center c) H H0).
Qed.

Lemma EqLineTwoPoints : forall A B : Point, forall d1 d2 : Line,
	A <> B ->
	OnLine d1 A ->
	OnLine d2 A ->
	OnLine d1 B ->
	OnLine d2 B ->
	EqLine d1 d2.
Proof.
	intros.
	apply EqLineTrans with (d2 := Ruler A B H).
	 apply EqLineDef; immediate11.
	 apply EqLineSym; apply EqLineDef; immediate11.
Qed.

Lemma EqLineOrEquiOriented : forall d1 d2 : Line,
	EqLine d1 d2 ->
	(EquiOriented (LineA d1) (LineB d1) (LineA d2) (LineB d2) /\
	EquiOriented (LineA d2) (LineB d2) (LineA d1) (LineB d1)) \/
	(EquiOriented (LineA d1) (LineB d1) (LineB d2) (LineA d2) /\
	EquiOriented (LineA d2) (LineB d2) (LineB d1) (LineA d1)).

Proof.
	intros; inversion H.
	destruct (TwoPointsOnLineOrientation (LineA d2) (LineB d2) d1 H0 H1).
	 left; split.
	  canonize1.
	    step11 H4.
	  immediate11.
	 right; split.
	  canonize1.
	    step11 H4.
	  immediate11.
Qed.

Lemma OnLineTwoPoints : forall A B C : Point, forall d : Line,
	A <> B ->
	OnLine d A ->
	OnLine d B ->
	Collinear A B C ->
	OnLine d C.
Proof.
	intros.
	assert (EqLine d (Ruler A B H)).
	 apply EqLineDef; simplLine1; immediate11.
	 apply (EqLineOnLine (Ruler A B H) d C).
	  apply EqLineSym; immediate11.
	  simplLine1; immediate11.
Qed.

End EQUAL_LINES.

