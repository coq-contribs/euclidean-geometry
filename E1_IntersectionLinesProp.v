Require Import A1_Plan A4_Droite A6_Intersection A7_Tactics.

Section INTERSECTION_LINES_PROPERTIES.

Definition InterLinesPoint (l1 l2 : Line) (H : SecantLines l1 l2) := 
let (M, _) := PointDef (fun M : Point => OnLine l1 M /\ OnLine l2 M) (InterLines l1 l2 H) in M.

Lemma OnLine1InterLinesPoint : forall (l1 l2 : Line) (H : SecantLines l1 l2),
	OnLine l1 (InterLinesPoint l1 l2 H).
Proof.
	intros; unfold InterLinesPoint in |- *.
	destruct (PointDef (fun M : Point => OnLine l1 M /\ OnLine l2 M) (InterLines l1 l2 H)) as (M, ((H1, _), _)).
 	exact H1.
Qed.

Lemma OnLine2InterLinesPoint : forall (l1 l2 : Line) (H : SecantLines l1 l2),
	OnLine l2 (InterLinesPoint l1 l2 H).
Proof.
	intros; unfold InterLinesPoint in |- *.
	destruct (PointDef (fun M : Point => OnLine l1 M /\ OnLine l2 M) (InterLines l1 l2 H)) as (M, ((_, H1), _)).
 	exact H1.
Qed.

Lemma UniqueInterLinesPoint : forall (l1 l2 : Line) (H : SecantLines l1 l2), forall M : Point,
	OnLine l1 M -> OnLine l2 M ->
	M = InterLinesPoint l1 l2 H.
Proof.
	intros; unfold InterLinesPoint in |- *.
	destruct (PointDef (fun M : Point => OnLine l1 M /\ OnLine l2 M) (InterLines l1 l2 H)) as (N, (_, H2)).
	 apply sym_eq; apply (H2 M); auto.
Qed.

Lemma EqPointsInterLines : forall (l1 l2 : Line) (H : SecantLines l1 l2), forall M N : Point,
	OnLine l1 M -> OnLine l2 M -> OnLine l1 N -> OnLine l2 N ->
	M = N.
Proof.
	intros; apply trans_eq with (y := InterLinesPoint l1 l2 H).
	 apply UniqueInterLinesPoint; trivial.
	 apply sym_eq; apply UniqueInterLinesPoint; trivial.
Qed.

Lemma SecantLinesSym : forall l1 l2 : Line, 	
	SecantLines l1 l2 -> SecantLines l2 l1.
Proof.
	unfold SecantLines, ParallelLines in |- *; canonize1.
Qed.

End INTERSECTION_LINES_PROPERTIES.
							