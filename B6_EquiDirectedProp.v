Section EQUIDIRECTED_PROP.

Lemma EquiDirectedRefl : forall A B : Point, EquiDirected A B A B.
Proof.
	canonize1.
Qed.

Lemma EquiDirectedSym : forall A B C D : Point, 
	EquiDirected A B C D -> EquiDirected C D A B.
Proof.
	canonize1.
Qed.

Lemma EquiDirectedPermutAB : forall A B C D : Point, 
	EquiDirected A B C D -> EquiDirected B A C D.
Proof.
	canonize1.
Qed.

Lemma EquiDirectedPermutCD: forall A B C D : Point, 
	EquiDirected A B C D -> EquiDirected A B D C.
Proof.
	canonize1.
Qed.

Lemma NotEquiDirectedSym : forall A B C D : Point, 
	~EquiDirected A B C D -> ~EquiDirected C D A B.
Proof.
	intros A B C D H; contrapose0 H; apply EquiDirectedSym; exact H.
Qed.

Lemma NotEquiDirectedPermutAB : forall A B C D : Point, 
	~EquiDirected A B C D -> ~EquiDirected B A C D.
Proof.
	intros A B C D H; contrapose0 H; apply EquiDirectedPermutAB; exact H.
Qed.

Lemma NotEquiDirectedPermutCD: forall A B C D : Point, 
	~EquiDirected A B C D -> ~EquiDirected A B D C.
Proof.
	intros A B C D H; contrapose0 H; apply EquiDirectedPermutCD; exact H.
Qed.

Lemma EquiDirectedCollinear : forall A B C : Point,
	EquiDirected A B C A -> Collinear A B C.
Proof.
	canonize1.
	 elim (NotClockwiseABA C A); auto.
	 elim (NotClockwiseABB A C); apply (ChangeSenseABCA _ _ _ H0 C H).
	 elim (NotClockwiseABB A C); auto.
	 elim (NotClockwiseABA C A); apply (ChangeSenseABAC _ _ _ H C H0).
	 elim (NotClockwiseABB A C); apply (ChangeSenseABCB _ _ _ H0 C H).
	 elim (NotClockwiseABA C A); auto.
	 elim (NotClockwiseABA C A); apply (ChangeSenseABBC _ _ _ H C H0).
	 elim (NotClockwiseABB A C); auto.
	 elim (NotClockwiseABB A B); apply H0; apply (ClockwiseCAB _ _ _ H).
	 elim (NotClockwiseABA B A); apply (ChangeSenseABBC _ _ _ H0); apply (ClockwiseBCA _ _ _ H).
	 elim (NotClockwiseABA B A); apply H; apply (ClockwiseCAB _ _ _ H0).
	 elim (NotClockwiseABB A B); apply (ChangeSenseABCB _ _ _ H); apply (ClockwiseBCA _ _ _ H0).
	 elim (NotClockwiseABA B A); apply (ChangeSenseABAC _ _ _ H0); apply (ClockwiseCAB _ _ _ H).
	 elim (NotClockwiseABB A B); apply H0; apply (ClockwiseBCA _ _ _ H).
	 elim (NotClockwiseABB A B); apply (ChangeSenseABCA _ _ _ H0); apply (ClockwiseCAB _ _ _ H).
	 elim (NotClockwiseABA B A); apply H0; apply (ClockwiseBCA _ _ _ H).
Qed.

Lemma CollinearEquiDirected : forall A B C : Point,
	Collinear A B C -> EquiDirected A B C A.
Proof.
	intros A B C H; destruct (CollinearTwoCases B C A (CollinearBCA A B C H)).
	 destruct (CollinearTwoCases A C B (CollinearACB A B C H)); canonize1.
	   do 4 right; left; intros.
	   apply (ChangeSenseABAC _ _ _ H0); auto.
	 destruct (CollinearTwoCases A B C H); canonize1.
	   do 3 right; left; intros.
	   apply (ChangeSenseABAC _ _ _ H0); auto.
Qed.

End EQUIDIRECTED_PROP.
