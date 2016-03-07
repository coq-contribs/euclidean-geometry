Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import B4_RaysProp B7_Tactics .
Require Import D5_Tactics .
Require Import E1_IntersectionLinesProp.

Section NOT_EQUIDIRECTED_INTERSECTION_POINT.

Lemma FourPointsSecantLine : forall A B C D,
	Clockwise A B C -> ~Clockwise A B D -> ~EquiDirected A B C D.
Proof.
	intros A B C D H H0 H1.
	from3 H (C <> D).
	 destruct (NotClockwiseTwoCases _ _ _ H0).
	  canonize1.
	   contradict1 H H4.
	   contradict1 H H1.
	   contradict1 H3 H4.
	   contradict1 H3 H1.
	   contradict1 H3 H4.
	   contradict1 H H1.
	   contradict1 H3 H4.
	   contradict1 H H4.
	  since3 (Collinear A B C).
	   unfold EquiDirected in H1; decompose [or] H1.
	    step3 H4.
	    step3 H5.
	    step3 H4.
	      right; left; immediate3.
	    step3 H5.
	      left; immediate3.
	    step3 H4.
	      left; immediate3.
	    step3 H5.
	      left; immediate3.
	    step3 H4.
	      left; immediate3.
	    step3 H4.
	      left; immediate3.
	   contradict1 H H4.
Qed.

Lemma NotEquidirectedDistinctAB : forall A B C D, ~EquiDirected A B C D -> A<>B.
Proof.
	canonize1; subst.
	elim H; intros M H9; absurd1 H9.
Qed.

Lemma NotEquidirectedDistinctCD : forall A B C D, ~EquiDirected A B C D -> C<>D.
Proof.
	canonize1; subst.
	elim H5; intros M H9; absurd1 H9.
Qed.

Definition NotEquiDirectedInterPoint : forall A B C D,
	~EquiDirected A B C D -> Point.
Proof.
	intros.
	setLine0 A B ipattern:(ab).
	 apply (NotEquidirectedDistinctAB _ _ _ _ H).
	 setLine0 C D ipattern:(cd).
	  apply (NotEquidirectedDistinctCD _ _ _ _ H).
	  assert (SecantLines ab cd).
	  immediate1.
	exact (InterLinesPoint ab cd H2).
Defined.

Lemma NotEquiDirectedInterPointCollinearAB : forall (A B C D : Point) (H : ~EquiDirected A B C D),
Collinear A B (NotEquiDirectedInterPoint A B C D H).
Proof.
	intros.
	unfold NotEquiDirectedInterPoint in |- *.
	apply (OnLine1InterLinesPoint (Ruler A B (NotEquidirectedDistinctAB A B C D H)) (Ruler C D (NotEquidirectedDistinctCD A B C D H)) H).
Qed.

Lemma NotEquiDirectedInterPointCollinearCD : forall (A B C D : Point) (H : ~EquiDirected A B C D),
Collinear C D (NotEquiDirectedInterPoint A B C D H).
Proof.
	intros.
	unfold NotEquiDirectedInterPoint in |- *.
	apply (OnLine2InterLinesPoint (Ruler A B (NotEquidirectedDistinctAB A B C D H)) (Ruler C D (NotEquidirectedDistinctCD A B C D H)) H).
Qed.

Lemma UniqueNotEquiDirectedInterPoint: forall (A B C D : Point)  (H : ~EquiDirected A B C D), forall M : Point,
	Collinear A B M ->
	Collinear C D M ->
	M = NotEquiDirectedInterPoint A B C D H.
Proof.
	intros.
	unfold NotEquiDirectedInterPoint in |- *.
	apply UniqueInterLinesPoint; simpl in |- *; immediate3.
Qed.

Lemma EqPointsNotEquiDirectedInter : forall (A B C D I J : Point) (H : ~EquiDirected A B C D),
	Collinear A B I -> Collinear A B J -> Collinear C D I -> Collinear C D J ->
	I = J.
Proof.
	intros.
	apply (EqPointsInterLines (Ruler A B (NotEquidirectedDistinctAB A B C D H)) (Ruler C D (NotEquidirectedDistinctCD A B C D H)) H); trivial.
Qed.

Lemma EqPointsNotCollinear : forall A B C M : Point,
	~Collinear A B C ->
	Collinear A B M ->
	Collinear A C M ->
	A = M.
Proof.
	intros.
	apply (EqPointsNotEquiDirectedInter A B A C A M); immediate3.
Qed.

End NOT_EQUIDIRECTED_INTERSECTION_POINT.
