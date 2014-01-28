Require Import A1_Plan A2_Orientation A7_Tactics.
Require Import B1_ClockwiseProp.

Section COLLINEAR_PROPERTIES.

Lemma CollinearAAB : forall A B, Collinear A A B.
Proof.
	canonize1;  elim (NotClockwiseAAB _ _ H).
Qed.

Lemma CollinearABA : forall A B, Collinear A B A.
Proof.
	canonize1.
	 elim (NotClockwiseABA _ _ H).
	 elim (NotClockwiseABB _ _ H).
Qed.

Lemma CollinearABB : forall A B, Collinear A B B.
Proof.
	canonize1.
	 elim (NotClockwiseABB _ _ H).
	 elim (NotClockwiseABA _ _ H).
Qed.

Lemma NotCollinearDistinctAB : forall A B C : Point,
	~Collinear A B C -> A <> B.
Proof.
	red in |- *; intros; subst.
	elim H; apply CollinearAAB.
Qed.

Lemma NotCollinearDistinctBC : forall A B C : Point,
	~Collinear A B C -> B <> C.
Proof.
	red in |- *; intros; subst.
	elim H; apply CollinearABB.
Qed.

Lemma NotCollinearDistinctCA : forall A B C : Point,
	~Collinear A B C -> C <> A.
Proof.
	red in |- *; intros; subst.
	elim H; apply CollinearABA.
Qed.

Lemma CollinearBCA : forall A B C,
	Collinear A B C -> Collinear B C A.
Proof.
	canonize1.
	 elim H0; apply ClockwiseCAB; trivial.
	 elim H1; apply ClockwiseBCA; trivial.
Qed.

Lemma CollinearCAB : forall A B C,
	Collinear A B C -> Collinear C A B.
Proof.
	intros; do 2 apply CollinearBCA; trivial.
Qed.

Lemma CollinearBAC : forall A B C,
	Collinear A B C -> Collinear B A C.
Proof.
	unfold Collinear in |- *; intuition.
Qed.

Lemma CollinearACB : forall A B C,
	Collinear A B C -> Collinear A C B.
Proof.
	intros; apply CollinearBAC; apply CollinearCAB; trivial.
Qed.

Lemma CollinearCBA : forall A B C,
	Collinear A B C -> Collinear C B A.
Proof.
	intros; apply CollinearBAC; apply CollinearBCA; trivial.
Qed.

Lemma CollinearNotClockwise : forall A B C,
	Collinear A B C -> ~Clockwise A B C.
Proof.
	canonize1.
Qed.

Lemma ClockwiseABCNotCollinear : forall A B C,
	Clockwise A B C -> ~Collinear A B C.
Proof.
	canonize1.
Qed.

Lemma ClockwiseBACNotCollinear : forall A B C,
	Clockwise B A C -> ~Collinear A B C.
Proof.
	canonize1.
Qed.

End COLLINEAR_PROPERTIES.
