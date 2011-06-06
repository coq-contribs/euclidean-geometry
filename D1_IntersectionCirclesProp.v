Section INTERSECTION_CIRCLES_PROPERTIES.

Definition IntersectionCirclesPoint (c1 c2 : Circle) (H : SecantCircles c1 c2) := 
let (M, _) := (InterCirclesPointDef c1 c2 H) in M.

Lemma OnCircle1IntersectionCirclesPoint : forall (c1 c2 : Circle) (H : SecantCircles c1 c2),
	OnCircle c1 (IntersectionCirclesPoint c1 c2 H).
Proof.
	intros; unfold IntersectionCirclesPoint in |- *.
	setInterCircles c1 c2 ipattern:J.
	exact Hoc.
Qed.

Lemma OnCircle2IntersectionCirclesPoint : forall (c1 c2 : Circle) (H : SecantCircles c1 c2),
	OnCircle c2 (IntersectionCirclesPoint c1 c2 H).
Proof.
	intros; unfold IntersectionCirclesPoint in |- *.
	setInterCircles c1 c2 ipattern:J.
	exact Hoc0.
Qed.

Lemma NotClockwiseIntersectionCirclesPoint : forall (c1 c2 : Circle) (H : SecantCircles c1 c2),
	~Clockwise (Center c2) (IntersectionCirclesPoint c1 c2 H) (Center c1).
Proof.
	intros; unfold IntersectionCirclesPoint in |- *.
	setInterCircles c1 c2 ipattern:J.
	exact Hck.
Qed.

Lemma UniqueIntersectionCirclesPoint : forall (c1 c2 : Circle) (H : SecantCircles c1 c2), forall M : Point,
	OnCircle c1 M -> OnCircle c2 M ->   ~Clockwise (Center c2) M (Center c1) ->
	M = IntersectionCirclesPoint c1 c2 H.
Proof.
	intros; unfold IntersectionCirclesPoint in |- *.
	setInterCircles c1 c2 ipattern:J.
	apply sym_eq; apply Hun; intuition.
Qed.

Lemma EqPointsIntersectionCircles : forall (c1 c2 : Circle) (H : SecantCircles c1 c2), forall M N : Point,
	OnCircle c1 M -> OnCircle c2 M ->  ~Clockwise (Center c2) M (Center c1) ->
	OnCircle c1 N -> OnCircle c2 N -> ~Clockwise (Center c2) N (Center c1) ->
	M = N.
Proof.
	intros; apply trans_eq with (y := IntersectionCirclesPoint c1 c2 H).
	 apply UniqueIntersectionCirclesPoint; trivial.
	 apply sym_eq; apply UniqueIntersectionCirclesPoint; trivial.
Qed.

Lemma EqThirdPoint : forall A B M N : Point,
	A <> B ->
	Distance A M = Distance A N -> 
	Distance B M = Distance B N ->  
	~Clockwise A M B ->
	~Clockwise A N B ->
	M = N.
Proof.
	intros.
	setCircle0 A A M ipattern:gamma1.
	setCircle0 B B M ipattern:gamma2.
	apply (EqPointsIntersectionCircles gamma2 gamma1); simplCircle2.
	 immediate2.
	 immediate2.
	 immediate2.
	 immediate2.
	 immediate2.
	 immediate2.
	 immediate2.
	 immediate2.
Qed.

End INTERSECTION_CIRCLES_PROPERTIES.
