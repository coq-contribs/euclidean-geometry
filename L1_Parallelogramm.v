Section PARALLELOGRAMM.

Inductive Parallelogramm (A B C D : Point) : Prop := 
	| Pllgm : forall  (Hac: A <> C) (Hbd : B <> D), MidPoint A C Hac = MidPoint B D Hbd -> Parallelogramm A B C D.

Lemma ParallelogrammRev  : forall A B C D : Point, 
	Parallelogramm A B C D -> Parallelogramm A D C B.
Proof.
	intros; inversion H.
	apply (Pllgm A D C B Hac (sym_not_eq Hbd)).
	step10 H0.
	immediate10.
Qed.

Lemma ParallelogrammPerm  : forall A B C D : Point, 
	Parallelogramm A B C D -> Parallelogramm B C D A.
Proof.
	intros; inversion H.
	apply (Pllgm B C D A Hbd (sym_not_eq Hac)).
	step10 H0.
	immediate10.
Qed.

Definition PCenter  :forall A B C D : Point, Parallelogramm A B C D -> Point.
Proof.
	intros A B C D H; destruct H.
	exact (MidPoint A C Hac).
Defined.

Lemma PCenterHyp : forall A B C D : Point, forall H1 H2 : Parallelogramm A B C D,
	PCenter A B C D H1 = PCenter A B C D H2.
Proof.
	intros; unfold PCenter in |- *; dependent inversion H1; dependent inversion H2; simpl in |- *.
	immediate10.
Qed.

Lemma PCenterBetweenAC : forall A B C D : Point, forall H : Parallelogramm A B C D,
	Between A (PCenter A B C D H) C.
Proof.
	intros A B C D H; unfold PCenter in |- *.
	dependent inversion H.
	immediate10.
Qed.

Lemma PCenterBetweenBD : forall A B C D : Point, forall H : Parallelogramm A B C D,
	Between B (PCenter A B C D H) D.
Proof.
	intros A B C D H; unfold PCenter in |- *.
	dependent inversion H.
	step10 e.
	immediate10.
Qed.

Lemma PCenterEqDistanceAC  : forall A B C D : Point, forall H : Parallelogramm A B C D, 
	Distance (PCenter A B C D H) A = Distance (PCenter A B C D H) C.
Proof.
	intros; unfold PCenter in |- *.
	dependent inversion H.
	immediate10.
Qed.

Lemma PCenterEqDistanceBD  : forall A B C D : Point, forall H : Parallelogramm A B C D, 
	Distance (PCenter A B C D H) B = Distance (PCenter A B C D H) D.
Proof.
	intros; unfold PCenter in |- *.
	dependent inversion H.
	rewrite e; immediate10.
Qed.

Lemma ParallelogrammTCongruentAKBCKD : forall A B C D : Point, forall H : Parallelogramm A B C D,
	TCongruent (Tr A (PCenter A B C D H) B) (Tr C (PCenter A B C D H) D).
Proof.
	intros A B C D H; unfold PCenter in |- *.
	dependent inversion H.
	step10 3.
	 immediate10.
	 step10 e; immediate10.
	 from10 e (Between B (MidPoint A C Hac) D).
	  since10 (Between A (MidPoint A C Hac) C).
	   since10 (OpposedAngles (MidPoint A C Hac) A B C D).
Qed.

Lemma ParallelogrammTCongruentBKCDKA : forall A B C D : Point, forall H : Parallelogramm A B C D,
	TCongruent (Tr B (PCenter A B C D H) C) (Tr D (PCenter A B C D H) A).
Proof.
	intros A B C D H; unfold PCenter in |- *.
	dependent inversion H.
	step10 3.
	 step10 e; immediate10.
	 immediate10.
	 from10 e (Between B (MidPoint A C Hac) D).
	  since10 (Between A (MidPoint A C Hac) C).
	   since10 (OpposedAngles (MidPoint A C Hac) B C D A).
Qed.

Lemma ParallelogrammABeqCD  : forall A B C D : Point, forall H : Parallelogramm A B C D, 
	Distance A B = Distance C D.
Proof.
	intros.
	assert (H0 := ParallelogrammTCongruentAKBCKD A B C D H).
	immediate10.
Qed.

Lemma ParallelogrammBCeqDA  : forall A B C D : Point, forall H : Parallelogramm A B C D, 
	Distance B C = Distance D A.
Proof.
	intros.
	assert (H0 := ParallelogrammTCongruentBKCDKA A B C D H).
	immediate10.
Qed.

Lemma UniquePCenter : forall A B C D K : Point, forall H : Parallelogramm A B C D,  
	(Between A K C /\ Distance A K = Distance K C) \/ (Between B K D /\ Distance B K = Distance K D) ->
	K = PCenter A B C D H.
Proof.
	intros; unfold PCenter in |- *; dependent inversion H.
	decompose [and or] H0.
	 step10 (MidPoint A C Hac).
	 rewrite e; step10 (MidPoint B D Hbd).
Qed.

Lemma ParallelogrammTCongruentABCCDA : forall A B C D : Point, forall H : Parallelogramm A B C D,
	TCongruent (Tr A B C) (Tr C D A).
Proof.
	intros.
	step10 1.
	 apply ParallelogrammABeqCD; immediate10.
	 apply ParallelogrammBCeqDA; immediate10.
Qed.

Lemma ParallelogrammTCongruentBCDDAB : forall A B C D : Point, forall H : Parallelogramm A B C D,
	TCongruent (Tr B C D) (Tr D A B).
Proof.
	intros.
	step10 1.
	 apply ParallelogrammBCeqDA; immediate10.
	 apply sym_eq; apply ParallelogrammABeqCD; immediate10.
Qed.

Lemma  ParallelogrammVertex4 : forall A B C : Point, forall  (Hac: A <> C) (Hbk : B <> MidPoint A C Hac),
	Parallelogramm A B C (SymmetricPoint B (MidPoint A C Hac) Hbk).
Proof.
	intros.
	setSymmetricPoint5 B (MidPoint A C Hac) ipattern:D; fold D in |- *.
	assert (Hbd : B <> D).
	 immediate10.
	 apply (Pllgm A B C D Hac Hbd).
	   byDefEqPoint10.
	   step10 H.
Qed.

Lemma ParallelogrammDistinctABDistinctCD : forall A B C D : Point,
	Parallelogramm A B C D ->
	A <> B ->
	C <> D.
Proof.
	intros; step10 (ParallelogrammABeqCD A B C D H).
Qed.

Lemma ParallelogrammDistinctBCDistinctDA: forall A B C D : Point,
	Parallelogramm A B C D ->
	B <> C ->
	D <> A.
Proof.
	intros; step10 (ParallelogrammBCeqDA A B C D H).
Qed.

Lemma ParallelogrammDistinctCDDistinctAB : forall A B C D : Point,
	Parallelogramm A B C D ->
	C <> D ->
	A <> B.
Proof.
	intros; assert (H1 := ParallelogrammABeqCD A B C D H).
	step10 H1.
Qed.

Lemma ParallelogrammDistinctDADistinctBC : forall A B C D : Point,
	Parallelogramm A B C D ->
	D <> A ->
	B <> C.
Proof.
	intros; assert (H1 := ParallelogrammBCeqDA A B C D H).
	step10 H1.
Qed.

End PARALLELOGRAMM.

