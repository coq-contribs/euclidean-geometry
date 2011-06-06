Section CLOCKWISE_PROPERTIES.

Lemma FigureDistinct : forall f : Figure, forall A B : Point,
	f A  -> ~f  B -> A <> B.
Proof.
	red in |- *; intros; subst.
	elim H0; trivial.
Qed.

Lemma ClockwiseBCA : forall A B C, 
	Clockwise A B C -> Clockwise B C A.
Proof.
	exact ClockwisePerm.
Qed.

Lemma ClockwiseCAB : forall A B C, 
	Clockwise A B C -> Clockwise C A B.
Proof.
	intros A B C H; do 2 apply ClockwisePerm; trivial.
Qed.

Lemma NotClockwiseAAB : forall A B, ~Clockwise A A B.
Proof.
	intros A B; destruct (ClockwiseAntisym A A B); trivial.
Qed.

Lemma NotClockwiseABA : forall A B , ~Clockwise A B A.
Proof.
	intros A B H; elim (NotClockwiseAAB A B); apply ClockwiseCAB; trivial.
Qed.

Lemma NotClockwiseABB : forall A B , ~Clockwise A B B.
Proof.
	intros A B H; elim (NotClockwiseAAB B A); apply ClockwiseBCA; trivial.
Qed.

Lemma ClockwiseDistinctAB : forall A B C,
	Clockwise A B C -> A <> B.
Proof.
	intros A B C H Hi; subst.
	elim (NotClockwiseAAB B C); trivial.
Qed.

Lemma ClockwiseDistinctBC : forall A B C,
	Clockwise A B C -> B <> C.
Proof.
	intros A B C H Hi; subst.
	elim (NotClockwiseABB A C); trivial.
Qed.

Lemma ClockwiseDistinctCA : forall A B C,
	Clockwise A B C -> C <> A.
Proof.
	intros A B C H Hi; subst.
	elim (NotClockwiseABA A B); trivial.
Qed.

Lemma ClockwiseNotClockwise : forall A B C,
	Clockwise A B C -> ~Clockwise B A C.
Proof.
	intros A B C H H0.
	destruct (ClockwiseAntisym A B C); intuition.
Qed.

End CLOCKWISE_PROPERTIES.
