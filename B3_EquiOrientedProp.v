Section EQUIORIENTED_PROP.

Lemma EquiOrientedAABC : forall A B C : Point,
	EquiOriented A A B C.
Proof.
	canonize1.
	elim (NotClockwiseAAB _ _ H).
Qed.

Lemma  EquiOrientedNotClockwiseABC : forall A B C D, EquiOriented A B C D -> ~Clockwise A B C.
Proof.
	canonize1.
	elim (NotClockwiseABA C D); auto.
Qed.

Lemma  EquiOrientedNotClockwiseABD : forall A B C D, EquiOriented A B C D -> ~Clockwise A B D.
Proof.
	canonize1.
	elim (NotClockwiseABB C D); auto.
Qed.

Lemma ChangeAllABC : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B C ->
	EquiOriented C D A B.
Proof.
	intros; apply ChangeSide.
	 apply ChangeSense; trivial.
	 auto.
Qed.

Lemma ChangeAllBCD : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear B C D ->
	EquiOriented C D A B.
Proof.
	intros; apply ChangeSense.
	 apply ChangeSide; auto.
	 apply (CollinearCBA _ _ _ H1).
Qed.

Lemma ChangeAll : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B C \/ Collinear B C D ->
	EquiOriented C D A B.
Proof.
	intros A B C D H H0 H1; destruct H1.
	 apply ChangeAllABC; trivial.
	 apply ChangeAllBCD; trivial.
Qed.

Lemma ChangeSenseABAC : forall A B C : Point,
	EquiOriented A B A C -> EquiOriented B A C A.
Proof.
	intros; apply (ChangeSense _ _ _ _ H).
	apply CollinearABA.
Qed.

Lemma EquiOrientedCollinearCA : forall A B C : Point,
	EquiOriented A B C A -> Collinear A B C.
Proof.
	canonize1.
	 elim (NotClockwiseABA C A); auto.
	 elim (NotClockwiseABA B A); apply (ChangeSide _ _ _ _ H).
	  apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H0).
	  apply (ClockwiseBCA _ _ _ H0).
Qed.

Lemma ChangeSenseABCA : forall A B C : Point,
	EquiOriented A B C A -> EquiOriented B A A C.
Proof.
	intros; apply ChangeSense.
	 trivial.
	 apply EquiOrientedCollinearCA; trivial.
Qed.

Lemma ChangeSenseABBC : forall A B C : Point,
	EquiOriented A B B C -> EquiOriented B A C B.
Proof.
	intros; apply ChangeSense.
	 trivial.
	 apply CollinearABB.
Qed.

Lemma EquiOrientedCollinearCB : forall A B C : Point,
	EquiOriented A B C B -> Collinear A B C.
Proof.
	canonize1.
	 elim (NotClockwiseABA C B); auto.
	 elim (NotClockwiseABA A B); apply (ChangeAllBCD _ _ _ _ H).
	  apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H0).
	  apply CollinearABA.
	  apply (ClockwiseCAB _ _ _ H0).
Qed.

Lemma EquiOrientedCollinearAC : forall A B C : Point,
	EquiOriented A B A C -> Collinear A B C.
Proof.
	intros; apply CollinearBAC.
	apply EquiOrientedCollinearCB.
	apply ChangeSenseABAC; trivial.
Qed.

Lemma EquiOrientedCollinearBC : forall A B C : Point,
	EquiOriented A B B C -> Collinear A B C.
Proof.
	intros; apply CollinearBAC.
	apply EquiOrientedCollinearCA.
	apply ChangeSenseABBC; trivial.
Qed.

Lemma ChangeSenseABCB : forall A B C : Point,
	EquiOriented A B C B -> EquiOriented B A B C.
Proof.
	intros; apply (ChangeSense _ _ _ _ H).
	apply (EquiOrientedCollinearCB _ _ _ H).
Qed.

Lemma ChangeAllABAC : forall A B C : Point,
	EquiOriented A B A C -> A <> B ->
	EquiOriented A C A B.
Proof.
	intros; apply ChangeSenseABCB.
	apply ChangeSide; trivial.
Qed.

Lemma ChangeAllABCA : forall A B C : Point,
	EquiOriented A B C A -> A <> B ->
	EquiOriented C A A B.
Proof.
	intros; apply ChangeSenseABCA.
	apply ChangeSide; trivial.
Qed.

Lemma ChangeAllABBC : forall A B C : Point,
	EquiOriented A B B C -> A <> B ->
	EquiOriented B C A B.
Proof.
	intros; apply ChangeSenseABBC.
	apply ChangeSide; trivial.
Qed.

Lemma ChangeAllABCB : forall A B C : Point,
	EquiOriented A B C B -> A <> B ->
	EquiOriented C B A B.
Proof.
	intros; apply ChangeSenseABAC.
	apply ChangeSide; trivial.
Qed.

Lemma SegmentEquiOriented : forall A B C : Point,
	B <> C -> Segment A C B -> 
	EquiOriented A B B C.
Proof.
	canonize1.
	apply (ChangeSide _ _ _ _ H2); auto.
Qed.

Lemma EquiOrientedTrans : forall A B C D E F : Point,
	EquiOriented A B C D -> EquiOriented C D E F ->
	EquiOriented A B E F.
Proof.
	canonize1.
Qed.

Lemma EquiOrientedTransCollinear : forall A B C D E : Point,
	Collinear B C D ->
	EquiOriented A B D E ->
	EquiOriented B C D E ->
	EquiOriented A C D E.
Proof.
	canonize1.
	decompose [or] (FourthPoint A C M B H).
	 elim (NotClockwiseABB B A).
	   apply (ChangeSide _ _ _ _ H0).
	  apply sym_not_eq; apply (ClockwiseDistinctCA _ _ _ H4).
	  apply (ChangeSense _ _ _ _ H1).
	   canonize1.
	   apply (ClockwiseBCA _ _ _ H4).
	 auto.
	 auto.
Qed.

Lemma EquiOrientedABCDNotCollinearABC : forall A B C D : Point,
	EquiOriented A B C D ->
	 (A<>B /\ Clockwise C D A) \/ (A<>B /\ Clockwise C D B) \/ Clockwise B A D ->
	~Collinear A B C.
Proof.
	intuition.
	 elim (NotClockwiseABA A B).
	   apply (ChangeAll _ _ _ _ H); intuition.
	 elim (NotClockwiseABB A B).
	   apply (ChangeAll _ _ _ _ H); intuition.
	 elim (NotClockwiseABA D C).
	   apply (ChangeSense _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotCollinearBCD : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Clockwise C D A ->
	~Collinear B C D .
Proof.
	intuition.
	elim (NotClockwiseABA A B).
	apply (ChangeAll _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotClockwiseCDA : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B C \/ Collinear B C D ->
	~Clockwise C D A.
Proof.
	intuition.
	 elim (NotClockwiseABA A B).
	   apply (ChangeAll _ _ _ _ H); intuition.
	 elim (NotClockwiseABA A B).
	   apply (ChangeAll _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotClockwiseDCA : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	~Clockwise D C A.
Proof.
	intuition.
	elim (NotClockwiseABB B A).
	apply (ChangeSide _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotClockwiseCDB : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	Collinear A B C->
	~Clockwise C D B.
Proof.
	intuition.
	elim (NotClockwiseABB A B).
	apply (ChangeAll _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotClockwiseDCB : forall A B C D : Point,
	EquiOriented A B C D ->
	A <> B ->
	~Clockwise D C B.
Proof.
	intuition.
	elim (NotClockwiseABA B A).
	apply (ChangeSide _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotClockwiseBAD : forall A B C D : Point,
	EquiOriented A B C D ->
	Collinear A B C ->
	~Clockwise B A D.
Proof.
	intuition.
	elim (NotClockwiseABA D C).
	apply (ChangeSense _ _ _ _ H); intuition.
Qed.

Lemma EquiOrientedABCDNotClockwiseBAC : forall A B C D : Point,
	EquiOriented A B C D ->
	C <> D ->
	Collinear B C D ->
	~Clockwise B A C.
Proof.
	intuition.
	generalize H2; apply (EquiOrientedABCDNotClockwiseCDB D C B A).
	 apply (ChangeSide _ _ _ _ H).
	   apply sym_not_eq; apply (ClockwiseDistinctAB _ _ _ H2).
	 auto.
	 apply CollinearCBA; trivial.
Qed.

Lemma OpenRaysClockwise : forall A B C D E : Point,
	Clockwise A B C -> 
	OpenRay A B D  ->
	OpenRay A C E ->
	Clockwise A D E.
Proof.
	canonize1.
	apply H0.
	apply ClockwiseBCA.
	apply (ChangeSense A C A E H1).
	 apply CollinearABA.
	 apply ClockwiseCAB; trivial.
Qed.

End EQUIORIENTED_PROP.
