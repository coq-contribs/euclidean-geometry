Section N_PARALLELOGRAMM.

Lemma StrictParallelogrammBECD : forall A B C D E : Point, 
	StrictParallelogramm A B C D ->
	Between A B E ->
	Distance A B = Distance B E ->
	StrictParallelogramm B E C D.
Proof.
	intros; DestructSP11 ipattern:H.
	apply EquiDistantStrictParallelogramm.
	 step10 H0.
	 step10 (StrictParallelogrammClockwiseBCD A B C D H).
	 step10 (ParallelogrammABeqCD A B C D H2).
	 assert (TCongruent (Tr A B D) (Tr B E C)).
	  step10 2.
	   step10 (ParallelogrammBCeqDA A B C D H2).
	   apply StrictParallelogrammExteriorAngles; immediate10.
	  step10 H4.
Qed.

Lemma StrictParallelogrammEACD : forall A B C D E : Point, 
	StrictParallelogramm A B C D ->
	Between E A B ->
	Distance E A = Distance A B ->
	StrictParallelogramm E A C D.
Proof.
	intros; DestructSP11 ipattern:H.
	apply StrictParallelogrammPerm.
	apply EquiDistantStrictParallelogramm.
	 step10 H0.
	   right; step10 (StrictParallelogrammClockwiseDAB A B C D H).
	 step10 (StrictParallelogrammClockwiseCDA A B C D H).
	 assert (TCongruent (Tr A D C) (Tr D A E)).
	  step10 3.
	   step10 H1.
	     step10 (ParallelogrammABeqCD A B C D H2).
	   assert (CongruentAngle C D A E A D).
	    apply (StrictParallelogrammAlternateAngles D A B C E).
	     do 3 apply StrictParallelogrammPerm; immediate10.
	     immediate10.
	    immediate10.
	  step10 H4.
	 step10 H1.
	   step10 (ParallelogrammABeqCD A B C D H2).
Qed.

Lemma StrictParallelogrammBEFC : forall A B C D E F : Point, 
	StrictParallelogramm A B C D ->
	Between A B E ->
	Distance A B = Distance B E ->
	Between D C F ->
	Distance D C = Distance C F ->
	StrictParallelogramm B E F C.
Proof.
	intros.
	apply (StrictParallelogrammBECD A B F C E).
 	do 2 apply StrictParallelogrammPerm.
 	  apply (StrictParallelogrammEACD C D A B F).
 	 do 2 apply StrictParallelogrammPerm; immediate10.
 	 immediate10.
 	 immediate10.
 	immediate10.
 	immediate10.
Qed.

Lemma StrictParallelogrammA1An1BnB0 : forall (A0 A1 B0 B1 : Point) (Ha : A0 <> A1) (Hb : B0 <> B1) (n : nat),
	StrictParallelogramm A0 A1 B1 B0 ->
	StrictParallelogramm (Graduation n A0 A1 Ha) (Graduation (S n) A0 A1 Ha) (Graduation (S n) B0 B1 Hb) (Graduation n B0 B1 Hb) .
Proof.
	intros; induction n.
	 repeat rewrite Graduation0; repeat rewrite Graduation1; immediate10.
	 apply (StrictParallelogrammBEFC (Graduation n A0 A1 Ha) (Graduation (S n) A0 A1 Ha) (Graduation (S n) B0 B1 Hb) (Graduation n B0 B1 Hb)); immediate10.
Qed.

End N_PARALLELOGRAMM.
