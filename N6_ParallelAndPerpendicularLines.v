Require Import A1_Plan A2_Orientation A4_Droite A7_Tactics .
Require Import B7_Tactics .
Require Import G1_Angles .
Require Import I2_Supplement .
Require Import K1_RightAngle .
Require Import L2_StrictParallelogramm L6_Tactics .
Require Import M1_SuperImposedLines M4_PerpendicularLines M5_Tactics .
Require Import N1_DrawingPerpendicularLines N5_UniqueParallel.

Section PARALLEL_AND_PERPENDICULAR_LINES.

Lemma RightRightEqMLine : forall A B C D : Point, forall Hab : A <> B, forall Hdb : D <> B,
	RightAngle A B C  ->
	RightAngle C B D ->
	EqLine (Ruler A B Hab) (Ruler D B Hdb).
Proof.
	intros.
	step12 Hab.
	since12 (~ Collinear A B C).
	 since12 (~ Collinear C B D).
	  by2Cases1 H1; by2Cases1 H2.
	   since12 (Supplement C B A D B C).
	    from12 H5 (Between A B D).
	   since12 (CongruentAngle A B C D B C).
	    from12 H5 (OpenRay B A D).
	   since12 (CongruentAngle C B A C B D).
	    from12 H5 (OpenRay B A D).
	   since12 (Supplement C B A D B C).
	    from12 H5 (Between A B D).
Qed.

Lemma PerpendicularPerpendicularParallel : forall d1 d2 d3 : Line,
	Perpendicular d1 d2 ->
	Perpendicular d2 d3 ->
	ParallelLines d1 d3.
Proof.
	intros.
	inversion H; inversion H0.
	by3Cases1 A B B0.
	 setStrictParallelogramm11 A B B0 ipattern:(E).
	   DestructSP11 H12.
	   since12 (RightAngle B B0 E).
	  as12 (Supplement B B0 E A B B0).
	    left; step12 H.
	  from12 H0 (RightAngle B B0 C0).
	    setLine0 A B ipattern:(d4).
	   immediate12.
	   since12 (EqLine d1 d4).
	    step12 (A, B).
	    step12 H18.
	      setLine0 E B0 ipattern:(d5).
	     immediate12.
	     setLine0 C0 B0 ipattern:(d6).
	      immediate12.
	      since12 (EqLine d5 d6).
	       unfold d5 in |- *; unfold d6 in |- *; apply (RightRightEqMLine E B0 B).
	        immediate12.
	        immediate12.
	       from12 (B0, C0) (EqLine d3 d6).
	         step12 H22.
	         step12 H21.
	 setStrictParallelogramm11 B0 B A ipattern:(E).
	   since12 (RightAngle B B0 E).
	  as12 (Supplement B B0 E A B B0).
	    left; step12 H.
	  from12 H0 (RightAngle B B0 C0).
	    setLine0 A B ipattern:(d4).
	   immediate12.
	   since12 (EqLine d1 d4).
	    step12 (A, B).
	    step12 H16.
	      setLine0 E B0 ipattern:(d5).
	     immediate12.
	     setLine0 C0 B0 ipattern:(d6).
	      immediate12.
	      since12 (EqLine d5 d6).
	       unfold d5 in |- *; unfold d6 in |- *; apply (RightRightEqMLine E B0 B).
	        immediate12.
	        immediate12.
	       from12 (B0, C0) (EqLine d3 d6).
	         step12 H20.
	         step12 H19.
	 from12 H12 (OnLine d1 B0).
	   since12 (SecantLines d1 d2).
	   from12 H13 (B0 = B).
	   subst.
	   from12 H0 (RightAngle C B C0).
	   setLine0 C0 B ipattern:(d4).
	  immediate12.
	  setLine0 A B ipattern:(d5).
	   immediate12.
	   since12 (EqLine d4 d5).
	    unfold d4 in |- *; unfold d5 in |- *; apply (RightRightEqMLine C0 B C).
	     immediate12.
	     immediate12.
	    from12 (A, B) (EqLine d1 d5).
	      step12 H18.
	      from12 (C0, B) (EqLine d3 d4).
	      step12 H19.
Qed.

Lemma UniquePerpendicular : forall d1 d2 d3 : Line, forall A : Point,
	Perpendicular d1 d3 ->
	Perpendicular d2 d3 ->
	OnLine d1 A ->
	OnLine d2 A ->
	EqLine d1 d2.
Proof.
	intros.
	since12 (ParallelLines d1 d2).
	 apply (PerpendicularPerpendicularParallel d1 d3 d2).
	  immediate12.
	  immediate12.
	 step12 H3.
Qed.

Lemma PerpendicularParallelPerpendicular : forall d1 d2 d3 : Line,
	Perpendicular d1 d2 ->
	ParallelLines d1 d3 ->
	Perpendicular d2 d3.
Proof.
	intros.
	setInterLines d3 d2 ipattern:(A).
	 apply (ParallelSecant d1); immediate12.
	 pose (d4 := PerpendicularUp d2 A Hol0).
	   assert (H1 := PerpendicularUpPerpendicular d2 A Hol0); fold d4 in H1.
	   since12 (ParallelLines d1 d4).
	  apply (PerpendicularPerpendicularParallel d1 d2 d4); immediate12.
	  since12 (OnLine d4 A).
	   apply (PerpendicularUpOnLine d2 A Hol0).
	   since12 (EqLine d3 d4).
	    apply (UniqueParallel d1 d3 d4 A); immediate12.
	    step12 H4.
Qed.

Lemma SecantPerpendicularSecant : forall d1 d2 d3 d4 : Line,
	SecantLines d1 d2 ->
	Perpendicular d1 d3 ->
	Perpendicular d2 d4 ->
	SecantLines d3 d4.
Proof.
	intros.
	contrapose0 H.
	apply (PerpendicularPerpendicularParallel d1 d3 d2 H0).
	apply PerpendicularSym; apply (PerpendicularParallelPerpendicular d4);
	 immediate12.
Qed.

Lemma SecantParallelSecant : forall d1 d2 d3 d4 : Line,
	SecantLines d1 d2 ->
	ParallelLines d1 d3 ->
	ParallelLines d2 d4 ->
	SecantLines d3 d4.
Proof.
	intros.
	contrapose0 H.
	apply (ParallelTrans d1 d3 d2 H0).
	apply (ParallelTrans d3 d4); immediate12.
Qed.

End PARALLEL_AND_PERPENDICULAR_LINES.
