Require Import A1_Plan A2_Orientation .
Require Import C1_Distance .
Require Import D1_IntersectionCirclesProp .
Require Import F5_Tactics .
Require Import G1_Angles.

Section ANGLE_PROPERTIES.

Lemma  EqAngleUniquePointSide1 : forall A B C D : Point, 
	CongruentAngle C A B D A B ->
	Distance A C = Distance A D ->
	~Clockwise A C B ->
	~Clockwise A D B ->
	C = D.
Proof.
	intros.
	apply (EqThirdPoint A B).
	 apply (CongruentAngleDistinctBC C A B D A B H) .
	 immediate5.
	 apply (CongruentSAS A B C A B D).
	  immediate5.
	  immediate5.
	  apply CongruentAngleRev; immediate5.
	 immediate5.
	 immediate5.
Qed.

Lemma  EqAngleUniquePointSide2 : forall A B C D : Point,
	CongruentAngle B A C B A D  ->
	Distance A C = Distance A D ->
	~Clockwise A B C ->
	~Clockwise A B D ->
	C = D.
Proof.
	intros.
	apply (EqThirdPoint B A).
	 apply sym_not_eq; apply (CongruentAngleDistinctBA B A C B A D H).
	 apply (CongruentSAS A B C A B D); immediate5.
	 immediate5.
	 immediate5.
	 immediate5.
Qed.

Lemma  EqAngleOpenRay1 : forall A B C D : Point, 
	CongruentAngle C A B D A B ->
	~Clockwise A C B ->
	~Clockwise A D B ->
	OpenRay A C D.
Proof.
	intros.
	setMarkSegmentPoint5 A D A C ipattern:(E).
	 apply (CongruentAngleDistinctED C A B D A B H).
	 since5 (C = E).
	  apply (EqAngleUniquePointSide1 A B C E).
	   apply (CongruentAngleTrans C A B D A B E A B).
	    immediate5.
	    apply CongruentAngleSide1.
	     immediate5.
	     apply (CongruentAngleDistinctBC C A B D A B H).
	     step5 H4.
	       step5 H3.
	       apply (CongruentAngleDistinctBA C A B D A B H).
	   immediate5.
	   immediate5.
	   intro; elim H1; step5 H4.
	  rewrite H5; immediate5.
Qed.

Lemma  EqAngleOpenRay2 : forall A B C D : Point, 
	CongruentAngle B A C B A D ->
	~Clockwise A B C ->
	~Clockwise A B D ->
	OpenRay A C D.
Proof.
	intros.
	setMarkSegmentPoint5 A D A C ipattern:(E).
	 apply (CongruentAngleDistinctEF B A C B A D H).
	 since5 (C = E).
	  apply (EqAngleUniquePointSide2 A B C E).
	   apply (CongruentAngleTrans B A C B A D B A E).
	    immediate5.
	    apply CongruentAngleSide2.
	     apply (CongruentAngleDistinctBA B A C B A D H).
	     immediate5.
	     step5 H4.
	       step5 H3.
	       apply (CongruentAngleDistinctBC B A C B A D H).
	   immediate5.
	   immediate5.
	   intro; elim H1; step5 H4.
	  rewrite H5; immediate5.
Qed.

End ANGLE_PROPERTIES.
