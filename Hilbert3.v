Load "Hilbert2.v".

Section CONGRUENCE.

(* Les axiomes de congruence sont verifies. *)

(* C1 : Given a line segment AB, and given a ray r originated at a point C, there exists a unique point D on the ray r such that AB ¤™ CD. *)

Lemma C1a : forall A B C D : Point, C <> D ->
	exists E : Point, ClosedRay C D E /\ Distance A B = Distance C E.
Proof.
	intros.
	setMarkSegment C D A B ipattern:E.
	answerIs E.
Qed.

Lemma C1b : forall A B C D E F : Point, C <> D ->
	ClosedRay C D E -> Distance A B = Distance C E -> 
	ClosedRay C D F -> Distance A B = Distance C F ->
	E = F.
Proof.
	intros.
	setMarkSegment C D A B ipattern:G.
	step G.
Qed.

(* C2 : If AB ¤™ CD and AB ¤™ EF, then CD ¤™ EF. Every line segment is congruent to itself. *)

Lemma C2a : forall A B C D E F : Point,
	Distance A B = Distance C D -> Distance A B = Distance E F ->
	Distance C D = Distance E F.
Proof.
	intros; immediate.
Qed.

Lemma C2b : forall A B : Point, Distance A B = Distance A B.
Proof.
	intros; immediate.
Qed.

(* C3 : Given three points A, B, C on a line satisfying A * B * C, and three further points D, E, F on a line satisfying D * E * F, if AB ¤™ DE and BC ¤™ EF, then AC ¤™ DF. *)

Lemma C3 : forall A B C D E F : Point,
	Between A B C -> Between D E F -> Distance A B = Distance D E -> Distance B C = Distance E F ->
	Distance A C = Distance D F.
Proof.
	intros.
	usingChasles A B C.
	step H1.
	step H2.
	usingChasles D E F.
Qed.

(* C4 : Given an angle ¡ÐBAC and given a ray DF, there exists a unique ray DE on a given side of the line DF, such that ¡ÐBAC ¤™ ¡ÐEDF. *)

Lemma C4a : forall A B C D F : Point,  A <> B -> A <> C -> D <> F ->
	exists E : Point, D <> E /\ ~Clockwise D F E /\ CongruentAngle B A C E D F.
Proof.
	intros.
	setMarkSegment D F A C ipattern:G.
	setTCongruent A C B D G ipattern:E.
	answerIs E.
	repeat split.
	 from H5 (Distance A B = Distance D E).
	   step H7.
	 contrapose H6.
	   step H3.
	   step H4.
	 from H5 (CongruentAngle B A C E D G).
	  from H5 (Distance A B = Distance D E).
	    step H7.
	  step H2.
	  step H7.
	    step H3.
Qed.

Lemma C4b : forall A B C D F : Point, A <> B -> A <> C -> D <> F ->
	exists E : Point, D <> E /\ ~Clockwise D E F /\ CongruentAngle B A C E D F.
Proof.
	intros.
	setMarkSegment D F A C ipattern:G.
	setTCongruent C A B G D ipattern:E.
	answerIs E.
	repeat split.
	 from H5 (Distance A B = Distance D E).
	   step H7.
	 contrapose H6.
	   step H3.
	   step H2.
	 from H5 (CongruentAngle B A C E D G).
	  step H4.
	  from H5 (Distance A B = Distance D E).
	    step H7.
	  step H7.
	    step H3.
Qed.

Lemma C4c : forall A B C D F E E' : Point, 
	~Clockwise D E F -> ~Clockwise D E' F -> 
	CongruentAngle B A C E D F ->CongruentAngle B A C E' D F ->
	OpenRay D E E'.
Proof.
	intros.
	from H1 (CongruentAngle E D F E' D F).
	step H3.
Qed.

Lemma C4d : forall A B C D F E E' : Point, 
	~Clockwise D F E -> ~Clockwise D F E' ->
	CongruentAngle B A C E D F -> CongruentAngle B A C E' D F ->
	OpenRay D E E'.
Proof.
	intros.
	from H1 (CongruentAngle F D E F D E').
	step H3.
Qed.

(* C5 : For any three angles ¥á, ¥â, ¥ã, if ¥á ¤™ ¥â and ¥á ¤™ ¥ã, then ¥â ¤™ ¥ã. Every angle is congruent to itself. *)

Lemma C5a : forall alpha : Point, IsAngle alpha -> alpha = alpha.
Proof.
	intros; immediate.
Qed.

Lemma C5b : forall alpha beta gamma : Point,
	IsAngle alpha -> IsAngle beta -> IsAngle gamma ->
	alpha = beta -> alpha = gamma -> beta = gamma.
Proof.
	intros.
	step H2.
Qed.

(* C6 (SAS): Given triangles ABC and DEF, suppose that AB ¤™ DE and AC ¤™ DF, and ¡ÐBAC ¤™ ¡ÐEDF. then the two triangles are congruent, namely, BC ¤™ EF, ¡ÐABC ¤™ ¡ÐDEF and ¡ÐACB ¤™ ¡ÐDFE. *)

Lemma C6a  : forall A B C D E F : Point, 
	Distance A B = Distance D E -> Distance A C = Distance D F -> CongruentAngle B A C E D F ->
	Distance B C = Distance E F.
Proof.
	intros.
	asWeHave (TCongruent (Tr B A C) (Tr E D F)).
Qed.

Lemma C6b  : forall A B C D E F : Point,  B <> C ->
	Distance A B = Distance D E -> Distance A C = Distance D F -> CongruentAngle B A C E D F ->
	CongruentAngle A B C D E F.
Proof.
	intros.
	asWeHave (TCongruent (Tr B A C) (Tr E D F)).
	asWeHave (Distance B C = Distance E F).
Qed.

Lemma C6c  : forall A B C D E F : Point, B <> C ->
	Distance A B = Distance D E -> Distance A C = Distance D F -> CongruentAngle B A C E D F ->
	CongruentAngle A C B D F E.
Proof.
	intros.
	asWeHave (TCongruent (Tr B A C) (Tr E D F)).
	asWeHave (Distance B C = Distance E F).
Qed.

End CONGRUENCE.
