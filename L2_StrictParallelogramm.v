Require Import A1_Plan A2_Orientation .
Require Import B1_ClockwiseProp B2_CollinearProp B7_Tactics .
Require Import C1_Distance .
Require Import F2_MarkSegment F5_Tactics .
Require Import G1_Angles .
Require Import H1_Triangles .
Require Import J2_MidPoint J4_Tactics .
Require Import K3_Tactics .
Require Import L1_Parallelogramm.

Section STRICT_PARALLELOGRAMM.

Inductive  StrictParallelogramm (A B C D : Point) : Prop := 
	| SPDef : Parallelogramm A B C D  -> Clockwise A B C -> StrictParallelogramm A B C D.

Implicit Arguments SPDef [A B C D].

Ltac DestructSP11 H := let Hp := fresh in let Hc := fresh in 
	((dependent inversion H as (Hp,Hc) || inversion H as (Hp,Hc)); simpl; clear H; pose (H := SPDef Hp Hc)).

Definition SPCenter (A B C D : Point) (H : StrictParallelogramm A B C D) := let (Hp, _) := H in (PCenter A B C D  Hp).

Lemma UniqueSPCenter : forall A B C D K : Point, forall H : StrictParallelogramm A B C D,  
	(Between A K C /\ Distance A K = Distance K C) \/ (Between B K D /\ Distance B K = Distance K D) ->
	K = SPCenter A B C D H.
Proof.
	intros.
	unfold SPCenter in |- *; dependent inversion H.
	apply UniquePCenter; intuition.
Qed.

Lemma StrictParallelogrammClockwiseABC : forall A B C D : Point,
	StrictParallelogramm A B C D -> Clockwise A B C.
Proof.
	intros A B C D (_, H); exact H.
Qed.

Lemma StrictParallelogrammClockwiseABK : forall (A B C D : Point) (H : StrictParallelogramm A B C D),
	Clockwise A B (SPCenter A B C D H).
Proof.
	intros; DestructSP11 ipattern:H.
	assert (H2 := PCenterBetweenAC A B C D H0).
	step10 H2.
Qed.

Lemma StrictParallelogrammClockwiseBCK : forall (A B C D : Point) (H : StrictParallelogramm A B C D),
	 Clockwise B C (SPCenter A B C D H).
Proof.
	intros; DestructSP11 ipattern:H.
	assert (H2 := PCenterBetweenAC A B C D H0).
	step10 H2.
Qed.

Lemma StrictParallelogrammClockwiseBCD : forall A B C D : Point,
	StrictParallelogramm A B C D -> Clockwise B C D.
Proof.
	intros; DestructSP11 ipattern:H.
	step10 (StrictParallelogrammClockwiseBCK A B C D H); simpl in |- *.
	assert (H2 := PCenterBetweenBD A B C D H0); immediate10.
Qed.

Lemma StrictParallelogrammClockwiseCDK : forall (A B C D : Point) (H :StrictParallelogramm A B C D ),
	Clockwise C D (SPCenter A B C D H).
Proof.
	intros; DestructSP11 ipattern:H.
	assert (H2 := StrictParallelogrammClockwiseBCK A B C D H); simpl in H2.
	step10 (PCenterBetweenBD A B C D H0).
Qed.

Lemma StrictParallelogrammClockwiseCDA : forall A B C D : Point,
	StrictParallelogramm A B C D -> Clockwise C D A.
Proof.
	intros; DestructSP11 ipattern:H.
	step10 (StrictParallelogrammClockwiseCDK A B C D H); simpl in |- *.
	assert (H2 := PCenterBetweenAC A B C D H0); immediate10.
Qed.

Lemma StrictParallelogrammClockwiseDAK : forall (A B C D : Point) (H : StrictParallelogramm A B C D),
	Clockwise D A (SPCenter A B C D H).
Proof.
	intros; DestructSP11 ipattern:H.
	assert (H2 := StrictParallelogrammClockwiseCDA A B C D H); simpl in H2.
	step10 (PCenterBetweenAC A B C D H0).
Qed.

Lemma StrictParallelogrammClockwiseDAB : forall A B C D : Point,
	StrictParallelogramm A B C D -> Clockwise D A B.
Proof.
	intros; DestructSP11 ipattern:H.
	step10 (StrictParallelogrammClockwiseDAK A B C D H); simpl in |- *.
	assert (H2 := PCenterBetweenBD A B C D H0); immediate10.
Qed.

Lemma StrictParallelogrammPerm  : forall A B C D : Point,
	StrictParallelogramm A B C D -> StrictParallelogramm B C D A.
Proof.
	intros; DestructSP11 ipattern:H.
	apply (SPDef (ParallelogrammPerm A B C D H0)).
	apply (StrictParallelogrammClockwiseBCD A B C D H).
Qed.

Lemma ClockwiseABKStrictParallelogramm : forall (A B C D : Point) (H : Parallelogramm A B C D),
	 Clockwise A B (PCenter A B C D H) -> StrictParallelogramm A B C D.
Proof.
	intros; apply (SPDef H).
	assert (H1 := PCenterBetweenAC A B C D H).
	step10 H1.
Qed.

Lemma ClockwiseBCKStrictParallelogramm : forall (A B C D : Point) (H : Parallelogramm A B C D),
	 Clockwise B C (PCenter A B C D H) -> StrictParallelogramm A B C D.
Proof.
	intros; apply (SPDef H).
	assert (H1 := PCenterBetweenAC A B C D H).
	step10 H1.
Qed.

Lemma ClockwiseBCDStrictParallelogramm : forall A B C D : Point,
	Parallelogramm A B C D ->
	 Clockwise B C D -> 
	StrictParallelogramm A B C D.
Proof.
	intros.
	apply (ClockwiseBCKStrictParallelogramm A B C D H).
	assert (H2 := PCenterBetweenBD A B C D H).
	step10 H2.
Qed.

Lemma ClockwiseCDKStrictParallelogramm : forall (A B C D : Point) (H : Parallelogramm A B C D),
	 Clockwise C D (PCenter A B C D H) -> StrictParallelogramm A B C D.
Proof.
	intros.
	apply (ClockwiseBCDStrictParallelogramm A B C D H).
	assert (H2 := PCenterBetweenBD A B C D H).
	step10 H2.
Qed.

Lemma ClockwiseCDAStrictParallelogramm : forall A B C D : Point,
	Parallelogramm A B C D ->
	 Clockwise C D A ->
	 StrictParallelogramm A B C D.
Proof.
	intros.
	apply (ClockwiseCDKStrictParallelogramm A B C D H).
	assert (H2 := PCenterBetweenAC A B C D H).
	step10 H2.
Qed.

Lemma ClockwiseDAKStrictParallelogramm : forall (A B C D : Point) (H : Parallelogramm A B C D),
	 Clockwise D A (PCenter A B C D H) -> StrictParallelogramm A B C D.
Proof.
	intros.
	apply (ClockwiseCDAStrictParallelogramm A B C D H).
	assert (H2 := PCenterBetweenAC A B C D H).
	step10 H2.
Qed.

Lemma ClockwiseDABStrictParallelogramm : forall A B C D : Point,
	Parallelogramm A B C D ->
	 Clockwise D A B -> 
	StrictParallelogramm A B C D.
Proof.
	intros.
	apply (ClockwiseDAKStrictParallelogramm A B C D H).
	assert (H2 := PCenterBetweenBD A B C D H).
	step10 H2.
Qed.

Lemma StrictParallelogrammDistinctAB : forall A B C D : Point,
	StrictParallelogramm A B C D -> A <> B.
Proof.
	intros; DestructSP11 ipattern:H.
	immediate10.
Qed.

Lemma StrictParallelogrammDistinctBC : forall A B C D : Point,
	StrictParallelogramm A B C D -> B <> C.
Proof.
	intros; DestructSP11 ipattern:H.
	immediate10.
Qed.

Lemma StrictParallelogrammDistinctCD : forall A B C D : Point,
	StrictParallelogramm A B C D -> C <> D.
Proof.
	intros.
	assert (H1 := StrictParallelogrammClockwiseCDA A B C D H).
	immediate10.
Qed.

Lemma StrictParallelogrammDistinctDA : forall A B C D : Point,
	StrictParallelogramm A B C D -> D  <> A.
Proof.
	intros.
	assert (H1 := StrictParallelogrammClockwiseCDA A B C D H).
	immediate10.
Qed.

Lemma EquiDistantStrictParallelogramm : forall A B C D : Point,
	Clockwise A B C ->
	Clockwise C D A ->
	Distance A B = Distance C D ->
	Distance B C = Distance D A ->
	StrictParallelogramm A B C D.
Proof.
	intros.
	setMidPoint9 A C ipattern:K.
	since10 (B <> D).
	 intro; subst B.
	   contradict1 H0 H.
	 from10 H4 (Clockwise A B K).
	  from10 H4 (Clockwise C D K).
	   from10 1 (TCongruent (Tr C D A) (Tr A B C)).
	    from10 2 (TCongruent (Tr A B K) (Tr C D K)).
	       from10 H4 (CongruentAngle K A B C A B).
	      from10 H4 (CongruentAngle K C D A C D).
	       step10 H10.
	         step10 H11.
	         step10 H9.
	     from10 H10 (CongruentAngle A K B C K D).
	      from10 H11 (Between B K D).
	       since10 (Parallelogramm A B C D).
	        apply (Pllgm A B C D H3 H6).
	          byDefEqPoint10.
	        apply SPDef; immediate10.
 Qed.

Lemma  StrictPVertex4 : forall A B C : Point, 
	Clockwise A B C -> Point.
Proof.
	intros.
	assert (A <> C).
	 immediate10.
	 setSymmetricPoint5 B (MidPoint A C H0) ipattern:D.
	  intro; assert (Collinear A B C).
	   rewrite H1; immediate10.
	   contradict1 H H2.
	  exact D.
Defined.

Lemma  StrictPVertex4Parallelogramm : forall A B C : Point, forall H : Clockwise A B C,
	 StrictParallelogramm A B C (StrictPVertex4 A B C H).
Proof.
	intros; assert (Parallelogramm A B C (StrictPVertex4 A B C H)).
	 unfold StrictPVertex4 in |- *.
	   apply ParallelogrammVertex4.
	 apply SPDef; immediate10.
Qed.

Lemma  UniqueStrictPVertex4 : forall A B C D : Point, forall H : Clockwise A B C,
	 StrictParallelogramm A B C D ->
	D = StrictPVertex4 A B C H.
Proof.
	intros; unfold StrictPVertex4 in |- *.
	inversion H0; simpl in |- *.
	inversion H1; simpl in |- *.
	step10  (SymmetricPoint B (MidPoint A C (sym_not_eq (ClockwiseDistinctCA A B C H)))  (fun H4 : B = MidPoint A C (sym_not_eq (ClockwiseDistinctCA A B C H)) =>  False_ind False  (ClockwiseABCNotCollinear A B C H (eq_ind_r (fun B0 : Point => Collinear A B0 C)  (CollinearACB A C  (MidPoint A C (sym_not_eq (ClockwiseDistinctCA A B C H))) (MidPointCollinearAB A C (sym_not_eq (ClockwiseDistinctCA A B C H)))) H4)))).
	 as10  (MidPoint A C (sym_not_eq (ClockwiseDistinctCA A B C H)) = MidPoint A C Hac).
	   step10 H3.
	   as10 (Between B (MidPoint B D Hbd) D).
	 as10  (MidPoint A C (sym_not_eq (ClockwiseDistinctCA A B C H)) = MidPoint A C Hac).
	   step10 H3.
Qed.

End STRICT_PARALLELOGRAMM.

Implicit Arguments SPDef [A B C D].

Ltac DestructSP11 H := let Hp := fresh in let Hc := fresh in 
	((dependent inversion H as (Hp,Hc) || inversion H as (Hp,Hc)); simpl; clear H; pose (H := SPDef Hp Hc)).

