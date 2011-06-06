Load "Hilbert1.v".

Section ORDERING.

(* Les axiomes d'ordre sont verifies. *)

(* B1 : If B is between A and C, then A, B, C are distinct points on a line, and also B is between C and A. *)

Lemma B1a : forall A B C, Between A B C -> A <> B.
Proof.
	intros; immediate.
Qed.

Lemma B1b : forall A B C, Between A B C -> B <> C.
Proof.
	intros; immediate.
Qed.

Lemma B1c : forall A B C, Between A B C -> C <> A.
Proof.
	intros; immediate.
Qed.

Lemma B1d : forall A B C, Between A B C -> Collinear A B C.
Proof.
	intros; immediate.
Qed.

Lemma B1e : forall A B C, Between A B C -> Between C B A.
Proof.
	intros; immediate.
Qed.

(* B2 : For any two distinct points A, B, there exists a points C such that B is between A and C. *)

Lemma B2 : forall A B, A <> B -> exists C : Point, Between A B C.
Proof.
	intros.
	setSymmetric A B ipattern:C.
	answerIs C.
Qed.

(* B3 : Given three distinct points on a line, one and only one of them is between the other two. *)

Lemma B3a : forall A B C, A <> B -> B <> C ->  C <> A -> Collinear A B C ->
	Between A B C \/ Between B C A \/ Between C A B.
Proof.
	intros.
	by3SegmentCases H2.
	step H3.
	 step H4.
	step H4.
Qed.

Lemma B3b : forall A B C, Between A B C -> ~Between B A C.
Proof.
	intros A B C H H0.
	from H0 (Between C A C).
	since (C <> C).
	absurdHyp H2.
Qed.

Lemma B3c : forall A B C, Between A B C -> ~Between A C B.
Proof.
	intros A B C H H0.
	from H (Between A B A).
	since (A <> A).
	absurdHyp H2.
Qed.

(* B4 : (Pasch). Let A, B, C be three noncollinear points, and let L be a line not containing any of A, B, C. If L contains a point D lying between A and B, 
then it must contain either a point lying between A and C or a point lying between B and C, but not both. *)

Lemma B4a : forall A B C M N,
	~Collinear A B C -> Between A M B -> ~Collinear A M N -> 
	~Collinear B M N -> ~Collinear C M N ->
	(exists P : Point, Collinear M N P /\ Between A P C) \/
	(exists P : Point, Collinear M N P /\ Between B P C).
Proof.
	intros.
	setLine M N ipattern:d.
	byPaschCases A B C M d ipattern:P.
	 contrapose H1; step H1.
	 contrapose H2; step H2.
	 contrapose H3; step H3.
	 left; answerIs P; from H10 (Collinear M N P).
	 right; answerIs P; from H10 (Collinear M N P).
Qed.

Lemma B4b : forall A B C M N P Q,
	~Collinear A B C -> Between A M B -> ~Collinear A M N -> ~Collinear B M N ->
	~Collinear C M N -> Collinear M N P -> Between A P C -> Collinear M N Q -> 
	Between B Q C -> False.
Proof.
	intros.
	since (M <> P).
	 contrapose H.
	   since (Collinear A P C).
	   since (A <> P).
	   step H8.
	   step H.
	 since (M <> Q).
	  contrapose H.
	    since (B <> Q).
	    asWeHave (Collinear B Q C).
	    step H.
	  since (P <> Q).
	   contrapose H.
	     since (C <> Q).
	     asWeHave (Collinear B Q C).
	     step H.
	   destruct (B3a M P Q); try immediate.
	    since (M <> N).
	      step H6.
	    elim H; split; intro.
	     since (Clockwise A C B).
	      step H7.
	       step H5.
	       step H11.
	       step H0.
	       step H5.
	      contradict H12 H13.
	     since (Clockwise A B C).
	      step H5.
	       step H0.
	       step H11.
	       step H5.
	       step H7.
	      contradict H12 H13.
	    destruct H11.
	     elim H; split; intro.
	      since (Clockwise A C B).
	       step H5.
	        step H7.
	         right; step H11.	
	        step H7.
	        step H0.
	       contradict H12 H13.
	      since (Clockwise A B C).
	       step H0.
	        step H7.
	        step H11.
	        step H7.
	         right; step H5.
	       contradict H12 H13.
	     elim H; split; intro.
	      since (Clockwise A C B).
	       step H0.
	        step H5.
	        step H11.
	        step H0.
	        step H7.
	       contradict H12 H13.
	      since (Clockwise A B C).
	       step H7.
	        step H0.
	        step H11.
	        step H5.
	        step H0.
	       contradict H12 H13.
Qed.

End ORDERING.
