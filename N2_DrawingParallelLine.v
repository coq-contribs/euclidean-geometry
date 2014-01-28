Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import B2_CollinearProp B5_BetweenProp B7_Tactics .
Require Import F5_Tactics .
Require Import J2_MidPoint J4_Tactics .
Require Import L1_Parallelogramm L2_StrictParallelogramm L6_Tactics .
Require Import M5_Tactics.

Section DRAWING_PARALLEL.

Definition Parallel : forall l1 : Line, forall A : Point,
	~OnLine l1 A -> Line.
Proof.
	destruct l1 as (B, C, H); simpl in |- *; intros.
	setMidPoint9 B A ipattern:K.
	setSymmetricPoint5 C K ipattern:D.
	 contrapose0 H0.
	   step12 H0.
	 setLine0 A D ipattern:l2.
	  contrapose0 H0.
	    since12 (A <> K).
	    as12 (Collinear B K A).
	    step12 H0.
	  exact l2.
Defined.

Ltac destructParallel l1 A H K D :=
	let B := fresh "B" in let C := fresh "C" in let H0 := fresh in (
	destruct l1 as (B, C, H0); simpl in |- *; intros;
	let H2 := fresh in (
	pose (H2 := sym_not_eq (NotCollinearDistinctCA B C A H));
	setMidPoint9 B A K;
	fold H2 K in |- *;
	let H5 := fresh in (
	pose (H5 := fun H4 : C = K =>  H (eq_ind_r (fun C0 : Point => Collinear B C0 A)
		(BetweenCollinear B K A (MidPointBetween B A H2)) H4));
	setSymmetricPoint5 C K D;
	fold H5 D in |- *))).

Lemma LineAParallel : forall l1 : Line, forall A : Point, forall H : ~OnLine l1 A,
	A = LineA (Parallel l1 A H).
Proof.
	intros; destructParallel ipattern:l1 ipattern:A ipattern:H ipattern:K ipattern:D; immediate12.
Qed.

Lemma OnLineAParallel : forall l1 : Line, forall A : Point, forall H : ~OnLine l1 A,
	OnLine (Parallel l1 A H) A.
Proof.
	intros; destructParallel ipattern:l1 ipattern:A ipattern:H ipattern:K ipattern:D; immediate12.
Qed.

Lemma ParallelClockwiseParallelogramm : forall l1 : Line, forall A : Point, forall H : ~OnLine l1 A,
	Clockwise (LineA l1) (LineB l1) A ->
	Parallelogramm (LineA l1) (LineB l1)  (LineA (Parallel l1 A H)) (LineB (Parallel l1 A H)).
Proof.
	intros l1 A H Hc; destructParallel l1 A H ipattern:K ipattern:D.
	unfold D, K in |- *; immediate12.
Qed.

Lemma ParallelAntiClockwiseParallelogramm : forall l1 : Line, forall A : Point, forall H : ~OnLine l1 A,
	Clockwise (LineB l1) (LineA l1) A ->
	Parallelogramm (LineB l1) (LineA l1)  (LineB (Parallel l1 A H)) (LineA (Parallel l1 A H)).
Proof.
	intros l1 A H Hc; destructParallel l1 A H ipattern:K ipattern:D.
	unfold D, K in |- *; immediate12.
Qed.

Lemma ParallelParallelLine : forall l1 : Line, forall A : Point, forall H : ~OnLine l1 A,
	ParallelLines l1 (Parallel l1 A H).
Proof.
	intros.
	since12 (~ Collinear (LineA l1) (LineB l1) A).
	 destruct l1; immediate12.
	 by2Cases1 H0.
	  unfold ParallelLines in |- *.
	    assert (H2 := ParallelClockwiseParallelogramm l1 A H H1).
	    immediate12.
	  assert (H2 := ParallelAntiClockwiseParallelogramm l1 A H H1).
	    unfold ParallelLines in |- *; immediate12.
Qed.

Lemma ParallelNotSecant : forall l1 : Line, forall A : Point, forall H : ~OnLine l1 A,
	~SecantLines l1 (Parallel l1 A H).
Proof.
	red in |- *; intros; elim H0.
	apply ParallelParallelLine.
Qed.

Lemma OnParallelVertexP4 : forall d : Line, forall A : Point, forall H : ~OnLine d A, 
	forall Hc : Clockwise (LineA d)  (LineB d) A,
	LineB (Parallel d A H) = StrictPVertex4 (LineA d)  (LineB d) A Hc.
Proof.
	intros; destructParallel ipattern:d ipattern:A ipattern:H ipattern:K ipattern:D.
	byDefEqPoint11.
	assert (Parallelogramm B C A D).
	 unfold D, K in |- *; immediate12.
	 step12 H7.
Qed.

Lemma OnParallelOppVertexP4 : forall d : Line, forall A : Point, forall H : ~OnLine d A, 
	forall Hc : Clockwise A (LineB d)  (LineA d),
	LineB (Parallel d A H) = StrictPVertex4 A (LineB d)  (LineA d) Hc.
Proof.
	intros; destructParallel ipattern:d ipattern:A ipattern:H ipattern:K ipattern:D.
	byDefEqPoint11.
	assert (Parallelogramm A C B D).
	 unfold D, K in |- *; immediate12.
	 step12 H7.
Qed.

End DRAWING_PARALLEL.
