Load "Hilbert3.v".

Section CONTINUITY.

(* D1 (Archimedes) : Given line segments AB and CD, there is a natural number n such that n copies of AB added together will be greater than CD. *)

Lemma D1 : forall A B C D : Point, A <> B ->
	exists n : nat, exists E : Point,
	OpenRay A B E /\ Distance A E = DistanceTimes n A B /\ DistanceLt (Distance C D) (Distance A E).
Proof.
	intros.
	setMarkSegment A B C D ipattern:F.
	destruct (ArchimedianDistanceLt A B F H) as (n, (H3, H4)).
	answerIs n.
	setGraduation n A B ipattern:E.
	answerIs E.
	split.
	 step H2.
	   since (Between A (Graduation n A B H) (Graduation (S n) A B H)).
	 split.
	  immediate.
	  step H0; step H5; immediate.
Qed.

(* D2 (Dedekind) : Suppose the points of a line l are divided into two nonempty subsets S, T in such a way that no point of S is between two points of T, and no point of T is between two points of S. Then there exists a unique point P such that for any A Å∏ S and any B Å∏ T, either A = P or B = P or the point P is between A and B. *)

(* D2 (Cantor) : For any infinite seqence of segments {AnBn}, n Å∏ N* of a straight line a with the property that AiBi is included into the inside segment Ai-1Bi-1 for all i = 2, 3, 4, Åc, and there is not a segment situated inside all the segments in the sequence under consideration, there is a point M on a belonging to the inside of each segment in the sequence. *)

(* These lemmas cannot be verified in a geometry with only ruler and compass as constructors. *)

End CONTINUITY.
