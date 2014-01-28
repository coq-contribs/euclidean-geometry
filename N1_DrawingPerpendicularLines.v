Require Import A1_Plan A2_Orientation A4_Droite A5_Cercle A7_Tactics .
Require Import B1_ClockwiseProp B4_RaysProp B7_Tactics .
Require Import C1_Distance C5_TriangularInequality .
Require Import D1_IntersectionCirclesProp D3_SecondDimension D5_Tactics .
Require Import F2_MarkSegment F5_Tactics .
Require Import J4_Tactics .
Require Import L6_Tactics .
Require Import M1_SuperImposedLines M4_PerpendicularLines M5_Tactics.

Section DRAWING_PERPENDICULAR.

Definition  PerpendicularDown : forall (l : Line) (A : Point),
	~OnLine l A -> Line.
Proof.
	intros.
	destruct l as (B, C, Hbc).
	setCircle0 B B A ipattern:c1.
	setCircle0 C C A ipattern:c2.
	setIntersectionCircles3 c1 c2 ipattern:D.
	 simpl in |- *; immediate11.
	 setIntersectionCircles3 c2 c1 ipattern:E.
	   setLine0 D E ipattern:d.
	  simpl in H; by2Cases1 H.
	   from12 E (A = E).
	     step12 H8.
	     step12 H3.
	   from12 D (A = D).
	     step12 H8.
	     step12 H6.
	  exact d.
Defined.

Ltac PerpendicularDownDef l A H B C Hbc H0 H1 D H2 E c1 c2 Hde := intros;
destruct l as (B, C, Hbc);
simpl in |- *;
simpl in H;
pose (H0 := TriangleSpecABCBAC B A C);
fold H0 in |- *;
pose (H1 := conj Hbc H0:SecantCircles (Compass B B A) (Compass C C A));
fold H1 in |- *;
setIntersectionCircles3 (Compass B B A) (Compass C C A) ipattern:D;
fold D in |- *;
pose
 (H5 :=
  SecantCirclesSym (Compass B B A) (Compass C C A) H1
  :SecantCircles (Compass C C A) (Compass B B A)); 
 fold H5 in |- *;
setIntersectionCircles3 (Compass C C A) (Compass B B A) ipattern:E;
 fold E in |- *;
pose
 (c1 :=
  fun H9 : Clockwise B C A =>
  eq_ind A (fun E0 : Point => D <> E0)
    (sym_not_eq
       (FigureDistinct (fun M : Point => Clockwise B C M) A D H9
          (fun H10 : Clockwise B C D =>
           False_ind False
             (NotClockwiseIntersectionCirclesPoint 
                (Compass B B A) (Compass C C A) H1 
                (ClockwiseBCA B C D H10))))) E
    (UniqueIntersectionCirclesPoint (Compass C C A) 
       (Compass B B A) H5 A
       (eq_ind (Distance B D)
          (fun delta0 : Point =>
           Distance C D = Distance C A ->
           Distance C E = Distance C A ->
           Distance B E = delta0 -> Distance C A = Distance C A)
          (fun Heq0 : Distance C D = Distance C A =>
           eq_ind (Distance C D)
             (fun delta2 : Point =>
              Distance C E = delta2 ->
              Distance B E = Distance B D -> delta2 = delta2)
             (fun Heq1 : Distance C E = Distance C D =>
              eq_ind (Distance C E)
                (fun delta1 : Point =>
                 Distance B E = Distance B D -> delta1 = delta1)
                (fun _ : Distance B E = Distance B D =>
                 refl_equal (Distance C E)) (Distance C D) Heq1)
             (Distance C A) Heq0) (Distance B A)
          (OnCircle1IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle2IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle1IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5)
          (OnCircle2IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5))
       (eq_ind (Distance B D)
          (fun delta0 : Point =>
           Distance C D = Distance C A ->
           Distance C E = Distance C A ->
           Distance B E = delta0 -> delta0 = delta0)
          (fun Heq0 : Distance C D = Distance C A =>
           eq_ind (Distance C D)
             (fun delta2 : Point =>
              Distance C E = delta2 ->
              Distance B E = Distance B D -> Distance B D = Distance B D)
             (fun (_ : Distance C E = Distance C D)
                (Heq1 : Distance B E = Distance B D) =>
              eq_ind (Distance B E) (fun delta : Point => delta = delta)
                (refl_equal (Distance B E)) (Distance B D) Heq1)
             (Distance C A) Heq0) (Distance B A)
          (OnCircle1IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle2IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle1IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5)
          (OnCircle2IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5))
       (ClockwiseNotClockwise A B C (ClockwiseCAB B C A H9))));
fold c1 in |- *;
pose
 (c2 :=
  fun H9 : Clockwise C B A =>
  eq_ind A (fun D0 : Point => D0 <> E)
    (FigureDistinct (fun M : Point => Clockwise C B M) A E H9
       (fun H10 : Clockwise C B E =>
        False_ind False
          (NotClockwiseIntersectionCirclesPoint (Compass C C A)
             (Compass B B A) H5 (ClockwiseBCA C B E H10)))) D
    (UniqueIntersectionCirclesPoint (Compass B B A) 
       (Compass C C A) H1 A
       (eq_ind (Distance B D)
          (fun delta0 : Point =>
           Distance C D = Distance C A ->
           Distance C E = Distance C A ->
           Distance B E = delta0 -> delta0 = delta0)
          (fun Heq0 : Distance C D = Distance C A =>
           eq_ind (Distance C D)
             (fun delta2 : Point =>
              Distance C E = delta2 ->
              Distance B E = Distance B D -> Distance B D = Distance B D)
             (fun (_ : Distance C E = Distance C D)
                (Heq1 : Distance B E = Distance B D) =>
              eq_ind (Distance B E) (fun delta : Point => delta = delta)
                (refl_equal (Distance B E)) (Distance B D) Heq1)
             (Distance C A) Heq0) (Distance B A)
          (OnCircle1IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle2IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle1IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5)
          (OnCircle2IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5))
       (eq_ind (Distance B D)
          (fun delta0 : Point =>
           Distance C D = Distance C A ->
           Distance C E = Distance C A ->
           Distance B E = delta0 -> Distance C A = Distance C A)
          (fun Heq0 : Distance C D = Distance C A =>
           eq_ind (Distance C D)
             (fun delta2 : Point =>
              Distance C E = delta2 ->
              Distance B E = Distance B D -> delta2 = delta2)
             (fun Heq1 : Distance C E = Distance C D =>
              eq_ind (Distance C E)
                (fun delta1 : Point =>
                 Distance B E = Distance B D -> delta1 = delta1)
                (fun _ : Distance B E = Distance B D =>
                 refl_equal (Distance C E)) (Distance C D) Heq1)
             (Distance C A) Heq0) (Distance B A)
          (OnCircle1IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle2IntersectionCirclesPoint (Compass B B A) 
             (Compass C C A) H1)
          (OnCircle1IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5)
          (OnCircle2IntersectionCirclesPoint (Compass C C A) 
             (Compass B B A) H5))
       (ClockwiseNotClockwise A C B (ClockwiseCAB C B A H9))));
fold c2 in |- *;
pose (Hde := or_ind c1 c2 (NotCollinearTwoCases B C A H)).

Lemma PerpendicularDownOnLine : forall (l : Line) (A : Point) (H : ~OnLine l A),
	OnLine (PerpendicularDown l A H) A.
Proof.
	PerpendicularDownDef ipattern:l ipattern:A ipattern:H ipattern:B ipattern:C
	 ipattern:Hbc ipattern:H0 ipattern:H1 ipattern:D ipattern:H2 ipattern:E
	 ipattern:c1 ipattern:c2 ipattern:Hde.
	by2Cases1 H.
	 from12 E (A = E).
	   step12 H10.
	 from12 D (A = D).
	   step12 H10.
Qed.

Lemma PerpendicularDownPerpendicular : forall (l : Line) (A : Point) (H : ~OnLine l A),
	Perpendicular l (PerpendicularDown l A H).
Proof.
	PerpendicularDownDef ipattern:l ipattern:A ipattern:H ipattern:B ipattern:C
	 ipattern:Hbc ipattern:H0 ipattern:H1 ipattern:D ipattern:H2 ipattern:E
	 ipattern:c1 ipattern:c2 ipattern:Hde.
	setMidLine9 D E ipattern:m.
	assert (EqLine m (Ruler B C Hbc)).
	 step12 Hbc.
 	  apply H10; immediate12.
	  apply H10; immediate12.
	 step12 H11.
	   unfold m in |- *; immediate12.
Qed.

Definition  PerpendicularUp : forall (l : Line) (A : Point),
	OnLine l A -> Line.
Proof.
	destruct l as (B, C, Hbc); simpl in |- *; intros.
	setAddSegmentPoint5 B C A B C ipattern:D.
	setSymmetricPoint5 D A ipattern:E.
	 step12 H1.
	 setMidLine9 D E ipattern:m.
	   exact m.
Defined.

Ltac PerpendicularUpDef l A H B C Hbc D Hda E Hde:= 
intros l A H; destruct l as (B, C, Hbc); simpl in H;
unfold PerpendicularUp in |- *;
setAddSegmentPoint5 B C A B C ipattern:D; fold D in |- *;
pose (Hda := DistinctEqDistanceDistinct B C D A Hbc
    (eq_ind_r
       (fun p : Point => Distance A D = Distance B C -> Distance B C = p)
       (fun Heq : Distance A D = Distance B C =>
        eq_ind_r (fun delta : Point => Distance B C = delta)
          (refl_equal (Distance B C)) Heq) (DistanceSym D A)
       (EqDistanceAddSegmentPoint B C A B C Hbc H))); 
 fold Hda in |- *;
setSymmetricPoint5 D A ipattern:E; fold E in |- *;
pose (Hde := BetweenDistinctAC D A E (BetweenSymmetricPoint D A Hda));
 fold Hde in |- *.

Lemma PerpendicularUpOnLine : forall (l : Line) (A : Point) (H : OnLine l A),
	OnLine (PerpendicularUp l A H) A.
Proof.
	PerpendicularUpDef ipattern:l ipattern:A ipattern:H ipattern:B ipattern:C
	 ipattern:Hbc ipattern:D ipattern:Hda ipattern:E ipattern:Hde.
	immediate12.
Qed.

Lemma PerpendicularUpPerpendicular : forall (l : Line) (A : Point) (H : OnLine l A),
	Perpendicular l (PerpendicularUp l A H).
Proof.
	PerpendicularUpDef ipattern:l ipattern:A ipattern:H ipattern:B ipattern:C ipattern:Hbc ipattern:D ipattern:Hda ipattern:E ipattern:Hde.
	from12 Hda (EqLine (Ruler D A Hda) (Ruler B C Hbc)).
	from12 H5 (EqLine (Ruler D E Hde) (Ruler B C Hbc)).
	 step12 Hda.
	 step12 H6.
Qed.

End DRAWING_PERPENDICULAR.
			
