Section OPPOSED_ANGLES.

Inductive OpposedAngles (A B C D E : Point) : Prop :=
	| OpposedAngleDef : Between B A D -> Between C A E -> OpposedAngles A B C D E .

Lemma OpposedCongruentAngles : forall A B C D E : Point, 
	OpposedAngles A B C D E ->
	CongruentAngle B A C D A E.
Proof.
	intros; inversion H.
	since7 (Supplement B A C C A D).
	 apply BetweenSupplementAngles; immediate7.
	 since7 (Supplement C A D D A E).
	  apply BetweenSupplementAngles; immediate7.
	  apply (SupplementSupplementCongruent B A C D A E C A D).
	   immediate7.
	   apply SupplementSym; immediate7.
Qed.

Lemma AntiClockwiseBetweenCongruentOpposedAngles : forall A B C D E : Point,
 	~Clockwise B A C ->
	~Clockwise D A E ->
	Between B A D -> 
	CongruentAngle B A C D A E ->
	OpposedAngles A B C D E.
Proof.
	intros; split.
	 immediate7.
	 apply (AntiClockwiseSupplementAnglesBetween A C D E).
	  contrapose0 H.
	    step7 H1.
	  immediate7.
	  apply (SupplementCongruentSupplement B A C D A E C A D).
	   apply BetweenSupplementAngles; immediate7.
	   immediate7.
Qed.

Lemma ClockwiseBetweenCongruentOpposedAngles : forall A B C D E : Point, 
	~Clockwise C A B ->
	~Clockwise E A D ->
	Between B A D -> 
	CongruentAngle B A C D A E ->
	OpposedAngles A B C D E.
Proof.
	intros; split.
	 immediate7.
	 apply (ClockwiseSupplementAnglesBetween A C D E).
	  contrapose0 H.
	    step7 H1.
	  immediate7.
	  apply (SupplementCongruentSupplement B A C D A E C A D).
	   apply BetweenSupplementAngles; immediate7.
	   immediate7.
Qed.

Lemma OpposedAnglesAntiClockwiseBetween : forall A B C D E : Point,
 	~Clockwise B A C ->
	~Clockwise D A E ->
	Between B A D -> 
	CongruentAngle B A C D A E ->
	Between C A E.
Proof.
	intros; since7 (OpposedAngles A B C D E).
	 apply AntiClockwiseBetweenCongruentOpposedAngles; immediate7.
	 inversion H3; immediate7.
Qed.

Lemma OpposedAnglesClockwiseBetween : forall A B C D E : Point, 
	~Clockwise C A B ->
	~Clockwise E A D ->
	Between B A D -> 
	CongruentAngle B A C D A E ->
	Between C A E.
Proof.
	intros; since7 (OpposedAngles A B C D E).
	 apply ClockwiseBetweenCongruentOpposedAngles; immediate7.
	 inversion H3; immediate7.
Qed.

End OPPOSED_ANGLES.
