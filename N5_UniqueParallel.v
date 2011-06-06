Section UNICITY_OF_THE_PARALLEL.

Lemma PaschLine : forall A B C D : Point, forall l : Line,
	~Collinear A B C ->
	Between A D B ->
	OnLine l D ->
	~OnLine l A ->
	~OnLine l B ->
	~OnLine l C ->
	(exists E : Point, Between A E C /\ OnLine l E) \/
	(exists F : Point, Between B F C /\ OnLine l F).
Proof.
	intros.
	destruct l; simplLine1.
	byApartCases3 A0 B0 D.
	 by2Cases1 H.

	  destruct (PaschABC A B C D A0 H6 H0).
	   contrapose0 H2; step12 H2.
	   contrapose0 H3; step12 H3.
	   contrapose0 H4; step12 H4.
	   destruct H7 as (P, (H8, H9)).
	     left; exists P; split.
	    immediate12.
	    step12 H8.
	   destruct H7 as (P, (H8, H9)).
	     right; exists P; split.
	    immediate12.
	    step12 H8.

	  destruct (PaschABC B A C D A0 H6).
	   immediate12.
	   contrapose0 H3; step12 H3.
	   contrapose0 H2; step12 H2.
	   contrapose0 H4; step12 H4.
	   destruct H7 as (P, (H8, H9)).
	     right; exists P; split.
	    immediate12.
	    step12 H8.
	   destruct H7 as (P, (H8, H9)).
	     left; exists P; split.
	    immediate12.
	    step12 H8.

	 by2Cases1 H.
	  destruct (PaschABC A B C D B0 H6 H0).
	   contrapose0 H2; step12 H2.
	   contrapose0 H3; step12 H3.
	   contrapose0 H4; step12 H4.
	   destruct H7 as (P, (H8, H9)).
	     left; exists P; split.
	    immediate12.
	    step12 H8.
	   destruct H7 as (P, (H8, H9)).
	     right; exists P; split.
	    immediate12.
	    step12 H8.

	  destruct (PaschABC B A C D B0 H6).
	   immediate12.
	   contrapose0 H3; step12 H3.
	   contrapose0 H2; step12 H2.
	   contrapose0 H4; step12 H4.
	   destruct H7 as (P, (H8, H9)).
	     right; exists P; split.
	    immediate12.
	    step12 H8.
	   destruct H7 as (P, (H8, H9)).
	     left; exists P; split.
	    immediate12.
	    step12 H8.
Qed.

Lemma SecantParallelClockwise : forall d0 d1 : Line, forall A : Point, forall H : ~OnLine d0 A,
	OnLine d1 A ->
	~OnLine d1 (LineA d0) ->
	~OnLine d1 (LineB d0) ->
	Clockwise (LineA d0) (LineB d0) A ->
	SecantLines d1 (Parallel d0 A H) ->
	SecantLines d0 d1.
Proof.
	intros.
	destruct (TwoPointsOnParallel d0 A H H3) as (D, (E, (H5, (H6, (H7, (H8, H9)))))).

	destruct (PaschLine D E (LineB d0) A d1).
	 from12 H7 (Clockwise E D (LineB d0)).
	 immediate12.
	 immediate12.
	 contrapose0 H4.
	   assert (EqLine d1 (Parallel d0 A H)).
	  step12 (A, D).
	    apply OnLineAParallel.
	  step12 H10.
	 contrapose0 H4.
	   assert (EqLine d1 (Parallel d0 A H)).
	  step12 (A, E).
	    apply OnLineAParallel.
	  step12 H10.
	 immediate12.
	
	 destruct H10 as (F, (H11, H12)).
	   destruct (PaschLine D (LineB d0) (LineA d0) F d1).
	  since12 (Clockwise D (LineA d0) (LineB d0)).
	  immediate12.
	  immediate12.
	  contrapose0 H4.
	    assert (EqLine d1 (Parallel d0 A H)).
	   step12 (A, D).
	     apply OnLineAParallel.
	   step12 H10.
	  immediate12.
	  immediate12.

	  destruct H10 as (G, (H13, H14)).
	    destruct (StrictParallelogrammExistM A D (LineA d0) (LineB d0) G) as (J, (H15, H16)).
	   immediate12.
	   immediate12.
	   step12 (LineA d0, LineB d0, (G, J)).
	    step12 H15.
	      intro; subst.
	      since12 (Clockwise G D (LineA d0)).
	      contradict1 H13 H10.
	    step12 H13.
	      right; immediate12.

	  destruct H10 as (G, (H13, H14)).
	    apply SecantLinesSym; step12 (G, A).
	    destruct d0; simplLine1; immediate12.
	 destruct H10 as (F, (H11, H12)).
	   destruct (StrictParallelogrammExistN E A (LineA d0) (LineB d0) F) as (K, (H13, H14)).
	  immediate12.
	  immediate12.
	  step12 (LineA d0, LineB d0, (A, K)).
	    step12 H13.
	    intro; subst.
	    since12 (Clockwise (LineB d0) E F).
	    contradict1 H11 H10.
Qed.

Lemma SecantParallel : forall d0 d1 : Line, forall A : Point, forall H : ~OnLine d0 A,
	OnLine d1 A ->
	SecantLines d1 (Parallel d0 A H) ->
	SecantLines d0 d1.
Proof.
	intros.
	destruct d0.
	destruct (OnOrNotOnLine d1 A0).
	 apply SecantLinesSym; step12 (A0, A).
	 destruct (OnOrNotOnLine d1 B).
	  apply SecantLinesSym; step12 (B, A).
	  since12 (~ Collinear A0 B A).
	    by2Cases1 H4.
	   apply (SecantParallelClockwise (Ruler A0 B n) d1 A H); immediate12.
	   as12 (EqLine (Ruler A0 B n) (Ruler B A0 (sym_not_eq n))).
	     since12 (~ OnLine (Ruler B A0 (sym_not_eq n)) A).
	    intro; elim H.
	      step12 H6.
	    apply (SecantParallelClockwise (Ruler B A0 (sym_not_eq n)) d1 A H7).
	     immediate12.
	     immediate12.
	     immediate12.
	     immediate12.
	     since12 (EqLine (Parallel (Ruler A0 B n) A H) (Parallel (Ruler B A0 (sym_not_eq n)) A H7)).
	      apply EqParallelOppLines.
	      step12 H8.
Qed.

Lemma EqParallel : forall d0 d1 : Line, forall A : Point, forall H : ~OnLine d0 A,
	OnLine d1 A ->
	ParallelLines d0 d1 ->
	EqLine d1 (Parallel d0 A H).
Proof.
	intros.
	destruct d1.
	byApartCases3 A0 B A.
	 destruct (OnOrNotOnLine (Parallel d0 A H) A0).
	  step12 (A0, A).
	    apply OnLineAParallel.
	  since12 (SecantLines (Ruler A0 B n) (Parallel d0 A H)).
	   step12 (A, A0).
	     apply OnLineAParallel.
	   since12 (SecantLines d0 (Ruler A0 B n)).
	    apply (SecantParallel d0 (Ruler A0 B n) A H); immediate12.
	    elim H5; immediate12.
	 destruct (OnOrNotOnLine (Parallel d0 A H) B).
	  step12 (B, A).
	    apply OnLineAParallel.
	  since12 (SecantLines (Ruler A0 B n) (Parallel d0 A H)).
	   step12 (A, B).
	     apply OnLineAParallel.
	   since12 (SecantLines d0 (Ruler A0 B n)).
	    apply (SecantParallel d0 (Ruler A0 B n) A H); immediate12.
	    elim H5; immediate12.
Qed.

Lemma UniqueParallel : forall d0 d1 d2: Line, forall A : Point, 
	OnLine d1 A ->
	OnLine d2 A ->
	ParallelLines d0 d1 ->
	ParallelLines d0 d2 ->
	EqLine d1 d2.
Proof.
	intros; destruct (OnOrNotOnLine d0 A).
	 intros; step12 d0.
	  step12 H1.
	  step12 H2.
	 step12 (Parallel d0 A H3).
	  apply EqParallel; immediate12.
	  apply EqLineSym; apply EqParallel; immediate12.
Qed.

Lemma ParallelSecant : forall d0 d1 d2 : Line,
	ParallelLines d0 d1 -> 
	SecantLines d0 d2 -> 
	SecantLines d1 d2.
Proof.
	intros.
	setInterLinesPoint4 d0 d2 ipattern:A.
	destruct (OnOrNotOnLine d1 A).
	 from12 H (EqLine d0 d1).
	   step12 H4.
	 apply (SecantParallel d1 d2 A H3).
	  immediate12.
	  since12 (EqLine d0 (Parallel d1 A H3)).
	   apply EqParallel; immediate12.
	   step12 H4.
Qed.

Lemma  ParallelTrans : forall d0 d1 d2 : Line,
	ParallelLines d0 d1 -> 
	ParallelLines d1 d2 -> 
	ParallelLines d0 d2.
Proof.
	intros; destruct d2.
	destruct (OnOrNotOnLine d0 A).
	 since12 (EqLine d0 (Ruler A B n)).
	   apply (UniqueParallel d1 d0 (Ruler A B n) A); immediate12.
	 destruct (OnOrNotOnLine (Parallel d0 A H1) B).
	  since12 (EqLine (Ruler A B n) (Parallel d0 A H1)).
	   step12 (A, B).
	     apply OnLineAParallel.
	   step12 H3.
	     apply ParallelParallelLine.
	  since12 (SecantLines (Ruler A B n) (Parallel d0 A H1)).
	   step12 (A, B).
	     apply OnLineAParallel.
	   since12 (SecantLines d1 (Parallel d0 A H1)).
	    apply (ParallelSecant (Ruler A B n)); immediate12.
	    since12 (SecantLines d0 (Parallel d0 A H1)).
	     apply (ParallelSecant d1); immediate12.
	     elim H5; apply ParallelParallelLine.
Qed.

End UNICITY_OF_THE_PARALLEL.
