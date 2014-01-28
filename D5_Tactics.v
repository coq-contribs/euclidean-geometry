Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D2_ExistsClockwise D3_SecondDimension D4_DistanceLt.


Ltac immNotClockwise3 := match goal with
	|  |- ~Clockwise ?A ?A _ => apply NotClockwiseAAB	
	|  |- ~Clockwise ?A _ ?A => apply NotClockwiseABA
	|  |- ~Clockwise _ ?A ?A => apply NotClockwiseABB

	| |- ~Clockwise _ (IntersectionCirclesPoint ?c1 ?c2 ?H) _ => let Hyp := fresh in (
					assert (Hyp := NotClockwiseIntersectionCirclesPoint c1 c2 H);
					simplCircle1; exact Hyp)

	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?A ?B ?C => exact H	
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?B ?C ?A => intro; elim H; immClockwise1
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?C ?A ?B => intro; elim H; immClockwise1

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?D => apply (EquiOrientedNotClockwiseABD _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?D ?A => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise1
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?D ?A ?B => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise1

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?C => apply (EquiOrientedNotClockwiseABC _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?C ?A => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise1
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?C ?A ?B => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise1

	|  |- ~Clockwise ?A ?B ?C => apply ClockwiseNotClockwise; immClockwise1 
	|  |- ~Clockwise ?A ?B ?C => apply CollinearNotClockwise; immCollinear1 
end.

Ltac immBetween3 :=  match goal with
	| H : Between ?A ?B ?C |- Between ?A ?B ?C => exact H
	| H : Between ?C ?B ?A |- Between ?A ?B ?C => apply (BetweenSym _ _ _ H)
end.

Ltac immSegment3 := match goal with
	| |- Segment ?A ?B ?A => apply SegmentABA
	| |- Segment ?A ?B ?B => apply SegmentABB
	| |- Segment Oo (DistancePlus?A ?B) ?A => apply IsDistanceSegmentDistancePlus; immIsDistance2 A
	| H : Segment ?A ?B ?C |- Segment ?A ?B ?C => exact H
	| H : Segment ?A ?B ?C |- Segment ?B ?A ?C => apply (SegmentSym _ _ _ H)
	| H : Between ?A ?B ?C |- Segment ?A ?C ?B => apply (BetweenSegment A B C H)
	| H : Between ?A ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (BetweenSegment A B C H)
	| H : Between ?C ?B ?A |- Segment ?A ?C ?B => apply (BetweenSegment A B C  (BetweenSym _ _ _ H))
	| H : Between ?C ?B ?A |- Segment ?C ?A ?B =>  apply SegmentSym; apply (BetweenSegment A B C  (BetweenSym _ _ _ H))
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?A ?C ?B => apply (EquiOrientedSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (EquiOrientedSegment A B C H)
	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immOpenRay3 := match goal with 
	| |- OpenRay ?A ?A ?B => apply OpenRayAAB
	| |- OpenRay ?A ?B ?B => apply OpenRayABB

	| |- OpenRay Oo (Distance _ _ ) Uu => apply ClosedRayOpenRay; apply IsDistanceDistance
	| |- OpenRay Oo (DistancePlus _ _ ) Uu => apply ClosedRayOpenRay; apply IsDistanceDistancePlus
	| |- OpenRay Oo (DistanceTimes _ _ _ ) Uu => apply ClosedRayOpenRay; apply IsDistanceDistanceTimes

	|  H : OpenRay ?A ?B ?C |- OpenRay ?A ?B ?C => trivial
	|  H : EquiOriented ?A ?B ?A ?C |- OpenRay ?A ?B ?C => unfold OpenRay; exact H
	| H : forall M : Point, Clockwise ?A ?B M -> Clockwise ?A ?C M |- OpenRay ?A ?B ?C => trivial

	| H : ClosedRay ?A ?B ?C |- OpenRay ?A ?C ?B => apply ClosedRayOpenRay; exact H

	| H : Between ?A ?B ?C |- OpenRay ?A ?B ?C => apply BetweenOpenRayAB; exact H
	| H : Between ?A ?B ?C |- OpenRay ?A ?C ?B => apply BetweenOpenRayAC; exact H
	| H : Between ?A ?B ?C |- OpenRay ?C ?A ?B => apply BetweenOpenRayCA; exact H
	| H : Between ?A ?B ?C |- OpenRay ?C ?B ?A => apply BetweenOpenRayCB; exact H

	| H : Segment ?A ?B ?C |- OpenRay ?A ?C ?B => apply SegmentOpenRayAC; exact H
	| H : Segment ?A ?B ?C |- OpenRay ?B ?C ?A => apply SegmentOpenRayAC; apply (SegmentSym _ _ _ H)
	| H : Segment ?A ?B ?C |- OpenRay ?A ?B ?C => apply SegmentOpenRayAB; [exact H | immDistinct1]
	| H : Segment ?A ?B ?C |- OpenRay ?B ?A ?C => apply SegmentOpenRayAB; [apply (SegmentSym _ _ _ H) | immDistinct1]

	| H : OpenRay ?A ?B ?C |- OpenRay ?A ?C ?B => apply OpenRaySym; [immDistinct1 | exact H]
	| H : ClosedRay ?A ?B ?C |- OpenRay ?A ?B ?C =>  apply OpenRaySym; [immDistinct1 | apply ClosedRayOpenRay; exact H]

	| H : Archimed ?A ?B ?C |- OpenRay ?A ?C ?B => apply ClosedRayOpenRay; apply (ArchimedianClosedRay A B C H)
end.

Ltac immClosedRay3 := apply OpenRayClosedRay; immOpenRay3.

Ltac immDistinct3 := match goal with
	| H : ?A <> ?B |- ?A <> ?B => exact H
	| H : ?A <> ?B |- ?B <> ?A => auto
	| H : ?A = ?B -> False |- ?A <> ?B => exact H
	| H : ?A = ?B -> False |- ?B <> ?A => auto
	| |- Oo <> Uu => exact DistinctOoUu
	| |- Uu <> Oo => apply sym_not_eq; exact DistinctOoUu
	| |- LineA ?l <> LineB ?l => apply (LineH l)
	| |- LineB ?l <> LineA ?l => apply (sym_not_eq (LineH l))
	| H : Clockwise ?A ?B ?C |- ?A <> ?B => exact (ClockwiseDistinctAB A B C H)
	| H : Clockwise ?A ?B ?C |- ?B <> ?A => apply sym_not_eq; exact (ClockwiseDistinctAB A B C H)
	| H : Clockwise ?A ?B ?C |- ?B <> ?C => exact (ClockwiseDistinctBC A B C H)
	| H : Clockwise ?A ?B ?C |- ?C <> ?B => apply sym_not_eq; exact (ClockwiseDistinctBC A B C H)
	| H : Clockwise ?A ?B ?C |- ?C <> ?A => exact (ClockwiseDistinctCA A B C H)
	| H : Clockwise ?A ?B ?C |- ?A <> ?C => apply sym_not_eq; exact (ClockwiseDistinctCA A B C H)
	| H : ~Collinear ?A ?B ?C |- ?A <> ?B => exact (NotCollinearDistinctAB A B C H)
	| H : ~Collinear ?A ?B ?C |- ?B <> ?A => apply sym_not_eq; exact (NotCollinearDistinctAB A B C H)
	| H : ~Collinear ?A ?B ?C |- ?B <> ?C => exact (NotCollinearDistinctBC A B C H)
	| H : ~Collinear ?A ?B ?C |- ?C <> ?B => apply sym_not_eq; exact (NotCollinearDistinctBC A B C H)
	| H : ~Collinear ?A ?B ?C |- ?C <> ?A => exact (NotCollinearDistinctCA A B C H)
	| H : ~Collinear ?A ?B ?C |- ?A <> ?C => apply sym_not_eq; exact (NotCollinearDistinctCA A B C H)
	| H : Between ?A ?B _ |- ?A <> ?B => apply (BetweenDistinctAB _ _ _ H)
	| H : Between ?A ?B _ |- ?B <> ?A => apply sym_not_eq; apply (BetweenDistinctAB _ _ _ H)
	| H : Between ?A _ ?C |- ?A <> ?C => apply (BetweenDistinctAC _ _ _ H)
	| H : Between ?A _ ?C |- ?C <> ?A => apply sym_not_eq; apply (BetweenDistinctAC _ _ _ H)
	| H : Between _ ?B ?C |- ?B <> ?C => apply (BetweenDistinctBC _ _ _ H)
	| H : Between _ ?B ?C |- ?C <> ?B => apply sym_not_eq; apply (BetweenDistinctBC _ _ _ H)

	| H : Distance ?A ?B <> Oo |- ?A <> ?B => apply (NotNullDistance A B H)
	| H : Distance ?A ?B <> Oo |- ?B <> ?A => apply sym_not_eq; apply (NotNullDistance A B H)
	| H : Oo <> Distance ?A ?B |- ?A <> ?B => apply (NotNullDistance A B (sym_not_eq H))
	| H : Oo <> Distance ?A ?B |- ?B <> ?A => apply sym_not_eq; apply (NotNullDistance A B (sym_not_eq H))

	| H : ?A <> ?B |- Distance ?A ?B <> Oo => apply (DistanceNotNull A B H)
	| H : ?A <> ?B |- Distance ?B ?A <> Oo => apply (DistanceNotNull B A (sym_not_eq H))
	| H : ?A = ?B -> False |- Distance ?A ?B <> Oo => apply (DistanceNotNull A B H)
	| H : ?A = ?B -> False |- Distance ?B ?A <> Oo => apply (DistanceNotNull B A (sym_not_eq H))
	| H : ?A <> ?B |- Oo <> Distance ?A ?B => apply sym_not_eq; apply (DistanceNotNull A B H)
	| H : ?A <> ?B |- Oo <> Distance ?B ?A => apply sym_not_eq; apply (DistanceNotNull B A (sym_not_eq H))
	| H : ?A = ?B -> False |- Oo <> Distance ?A ?B => apply sym_not_eq; apply (DistanceNotNull A B H)
	| H : ?A = ?B -> False |- Oo <> Distance ?B ?A => apply sym_not_eq; apply (DistanceNotNull B A (sym_not_eq H))
end.

Ltac immTriangularInequality3 := match goal with
	| |- TriangularInequality ?A ?B ?B ?C ?A ?C => apply TriangularInequalityABBCAC
	| |- TriangularInequality ?A ?B ?B ?C ?C ?A => apply TriangularInequalityABBCCA
	| |- TriangularInequality ?A ?B ?C ?B ?A ?C => apply TriangularInequalityABCBAC
	| |- TriangularInequality ?A ?B ?C ?B ?C ?A => apply TriangularInequalityABCBCA
	| |- TriangularInequality ?B ?A ?B ?C ?A ?C => apply TriangularInequalityBABCAC
	| |- TriangularInequality ?B ?A ?B ?C ?C ?A => apply TriangularInequalityBABCCA
	| |- TriangularInequality ?B ?A ?C ?B ?A ?C => apply TriangularInequalityBACBAC
	| |- TriangularInequality ?B ?A ?C ?B ?C ?A => apply TriangularInequalityBACBCA
	| |- TriangularInequality ?A ?B ?A ?B ?A ?B => apply EquilateralInequality
end.

Ltac immTriangleSpec3 := match goal with
	| |- TriangleSpec ?A ?B ?B ?C ?A ?C => apply TriangleSpecABBCAC
	| |- TriangleSpec ?A ?B ?B ?C ?C ?A => apply TriangleSpecABBCCA
	| |- TriangleSpec ?A ?B ?C ?B ?A ?C => apply TriangleSpecABCBAC
	| |- TriangleSpec ?A ?B ?C ?B ?C ?A => apply TriangleSpecABCBCA
	| |- TriangleSpec ?B ?A ?B ?C ?A ?C => apply TriangleSpecBABCAC
	| |- TriangleSpec ?B ?A ?B ?C ?C ?A => apply TriangleSpecBABCCA
	| |- TriangleSpec ?B ?A ?C ?B ?A ?C => apply TriangleSpecBACBAC
	| |- TriangleSpec ?B ?A ?C ?B ?C ?A => apply TriangleSpecBACBCA
	| |- TriangleSpec?A ?B ?A ?B ?A ?B => apply EquilateralTriangleSpec
end.

Ltac immOnCircle3 := match goal with
	| H : OnCircle ?c ?A |- OnCircle ?c ?A => exact H
	| |- OnCircle (Compass _ _ _) _ => simpl; solveDistance2
	| |- OnCircle ?c _ => unfold c; simpl; solveDistance2

	| |- OnCircle ?c (IntersectionCirclesPoint ?c _ _) => apply OnCircle1IntersectionCirclesPoint
	| |- OnCircle ?c (IntersectionCirclesPoint _ ?c _) => apply OnCircle2IntersectionCirclesPoint
end.

Ltac solveEq3 := match goal with
	| |- ?X = ?X => apply refl_equal
	| H : ?X = ?Y |- ?X = ?Y => exact H
	| H : ?Y = ?X |- ?X = ?Y => rewrite H; apply refl_equal

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle3 | immOnCircle3 | immNotClockwise3]
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle3 | immOnCircle3 | immNotClockwise3]

	| |- ?X = _ => unfold X; solveEq2
	| |- _ = ?Y => unfold Y; solveEq2
end.

Ltac immDistanceLt3 := match goal with
	| |- DistanceLt ?A (DistancePlus ?A _) => apply DistanceLtDistancePlus; immediate2
	| |- DistanceLt ?A (DistancePlus _ ?A) => rewrite DistancePlusCommut; apply DistanceLtDistancePlus; immediate2

	| H : Between ?A ?C ?B |- DistanceLt (Distance ?A ?C) (Distance ?A ?B) => apply (BetweenDistanceLt A C B H)
	| H : Between ?A ?C ?B |- DistanceLt (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B H)
	| H : Between ?A ?C ?B |- DistanceLt (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (BetweenDistanceLt A C B H)
	| H : Between ?A ?C ?B |- DistanceLt (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B H)

	| H : Between ?B ?C ?A |- DistanceLt (Distance ?A ?C) (Distance ?A ?B) => apply (BetweenDistanceLt A C B (BetweenSym B C A H))
	| H : Between ?B ?C ?A |- DistanceLt (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B (BetweenSym B C A H))
	| H : Between ?B ?C ?A |- DistanceLt (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (BetweenDistanceLt A C B (BetweenSym B C A H))
	| H : Between ?B ?C ?A |- DistanceLt (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B (BetweenSym B C A H))

	| |- DistanceLt _ _ => unfold DistanceLe; immediate2
end.

Ltac immediate3 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate3
	| |- ?A \/ ?B => (left; immediate3)  || (right; immediate3)

	| |- DistancePlus _ _ = _ => solveDistance2
	| |- _ = DistancePlus _ _ => solveDistance2

	| |- DistanceTimes _ _ _ = _ => solveDistance2
	| |- _ = DistanceTimes _ _ _ => solveDistance2

	| |- Distance _ _ = _ => solveDistance2
	| |- _ = Distance _ _ => solveDistance2

	| |- IsDistance ?d => immIsDistance2 d

	| |- _ = _ => solveEq3
	| |- _ <> _ => immDistinct3
	| |- ?A = ?B -> False => fold(A <> B); immDistinct3

	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise3
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise3

	| |- Collinear _ _ _ => immCollinear2
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1

	| |- EquiOriented _ _ _ _ => immEquiOriented2
	| |- OpenRay _ _ _ => immOpenRay3
	| |- ClosedRay _ _ _ => immClosedRay3
	| |- Between _ _ _ => immBetween3
	| |- Segment _ _ _ => immSegment3
	| |- EquiDirected _ _ _ _ => immEquiDirected1
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected1
	| |- EquiDirected ?A ?B ?C ?D  -> False =>fold (~EquiDirected A B C D); immNotEquiDirected1

	| |- DistanceLe _ _ => immDistanceLe2
	| |- DistanceLt _ _ => immDistanceLt3
	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality3
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec3

	| |- Diameter _ _ => immDiameter2
	| |- OnCircle _ _ => immOnCircle3
end.

Ltac stepDistinct3 A B H := match type of H with

	| A <> ?C => apply (DistinctOrDistinctABC A C B H); try solve [left; immediate3 | right; left; immediate3 | do 2 right; immediate3]
	| ?C <> A => apply (DistinctOrDistinctABC A C B (sym_not_eq H));  try solve [left; immediate3 | right; left; immediate3 | do 2 right; immediate3]
	| B <> ?C => apply sym_not_eq; apply (DistinctOrDistinctABC B C A H); try solve [left; immediate3 | right; left; immediate3 | do 2 right; immediate3]
	| ?C <> B => apply sym_not_eq; apply (DistinctOrDistinctABC B C A (sym_not_eq H)); try solve [left; immediate3 | right; left; immediate3 | do 2 right; immediate3]

	| ?C <> ?D => apply (DistinctOrDistinct C D A B H); try solve [left; immediate3 | right; immediate3]

	| Distance ?C ?D = Distance A B =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate3 | exact H]
	| Distance ?C ?D = Distance B A =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate3 | immediate3]
	| Distance A B = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate3 | immediate3]
	| Distance B A = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate3 | immediate3]

	| ?d = Distance A B =>  apply (DistanceEqDistanceDistinct A B d); [try immediate3 | immediate3]
	| ?d = Distance B A =>  apply (DistanceEqDistanceDistinct A B d); [try immediate3 | immediate3]
	| Distance A B = ?d =>  apply (DistanceEqDistanceDistinct A B d); [try immediate3 | immediate3]
	| Distance B A = ?d =>  apply (DistanceEqDistanceDistinct A B d); [try immediate3 | immediate3]

	| OpenRay A ?C B => apply (OpenRayDistinct A C B); [try immediate3 | exact H]
	| OpenRay B ?C A => apply sym_not_eq; apply (OpenRayDistinct B C A); [try immediate3 | exact H]

	| EquiOriented ?C ?D A B => apply (EquiOrientedDistinct C D A B);  [try immediate3 | exact H]
	| EquiOriented ?C ?D B A =>  apply sym_not_eq; apply (EquiOrientedDistinct C D B A);  [try immediate3 | exact H]

	| Clockwise ?C ?D A => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate3 | try immediate3]
	| Clockwise ?D A ?C => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate3 | try immediate3]
	| Clockwise A ?C ?D => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate3 | try immediate3]
	| Clockwise ?C ?D B => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate3 | try immediate3]
	| Clockwise ?D B ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate3 | try immediate3]
	| Clockwise B ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate3 | try immediate3]

	| Collinear ?C ?D A => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate3 | try immediate3]
	| Collinear ?D A ?C => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate3 | try immediate3]
	| Collinear A ?C ?D => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate3 | try immediate3]
	| Collinear ?C ?D B => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate3 | try immediate3]
	| Collinear ?D B ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate3 | try immediate3]
	| Collinear B ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate3 | try immediate3]

	| ~Clockwise ?C ?D B => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate3 | try immediate3]
	| ~Clockwise ?D B ?C => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate3 | try immediate3]
	| ~Clockwise B ?C ?D => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate3 | try immediate3]
	| ~Clockwise ?C ?D A => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate3 | try immediate3]
	| ~Clockwise ?D A ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate3 | try immediate3]
	| ~Clockwise A ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate3 | try immediate3]

	| ~Collinear ?C ?D B => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate3 | try immediate3]
	| ~Collinear ?D B ?C => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate3 | try immediate3]
	| ~Collinear B ?C ?D => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate3 | try immediate3]
	| ~Collinear ?C ?D A => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate3 | try immediate3]
	| ~Collinear ?D A ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate3 | try immediate3]
	| ~Collinear A ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate3 | try immediate3]

	| Distance ?C ?D = Distance A B =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 
	| Distance A B = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 
	| Distance ?C ?D = Distance B A =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 
	| Distance B A = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 

	| ?C = ?D => (rewrite H || rewrite <- H || apply (DistinctEqDistanceDistinct C D A B)); try immediate2 
end.

Ltac stepBetweenClockwise3 H := match type of H with
	| Between ?A ?B ?C => match goal with
			| |- Clockwise A C ?M => apply (BetweenClockwiseOrClockwiseAC A B C M H); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise ?M A C => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAC A B C M H); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise C ?M A => apply ClockwiseBCA; apply (BetweenClockwiseOrClockwiseAC A B C M H); try solve [left;  immediate3 | right; immediate3]

			| |- Clockwise A B ?M => apply (BetweenClockwiseOrClockwiseAB A B C M H); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise ?M A B => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAB A B C M H); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise B ?M A => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseAB A B C M H); try solve [left;  immediate3 | right; immediate3]

			| |- Clockwise B C ?M =>  apply (BetweenClockwiseOrClockwiseBC A B C M H); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise ?M B C => apply ClockwiseCAB;  apply (BetweenClockwiseOrClockwiseBC A B C M H); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise C ?M B => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseBC A B C M H); try solve [left;  immediate3 | right; immediate3]
		end

	| Between ?C ?B ?A => match goal with
			| |- Clockwise A C ?M => apply (BetweenClockwiseOrClockwiseAC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise ?M A C => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]					| |- Clockwise C ?M A => apply ClockwiseBCA; apply (BetweenClockwiseOrClockwiseAC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]

			| |- Clockwise A B ?M => apply (BetweenClockwiseOrClockwiseAB A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise ?M A B => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAB A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise B ?M A => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseAB A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]

			| |- Clockwise B C ?M =>  apply (BetweenClockwiseOrClockwiseBC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise ?M B C => apply ClockwiseCAB;  apply (BetweenClockwiseOrClockwiseBC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]
			| |- Clockwise C ?M B => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseBC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate3 | right; immediate3]
		end
end.

Ltac stepClockwise3 A B C H := match type of H with

	| OpenRay _ _ _ => unfold OpenRay in H; stepOpenRayClockwise1 H
	| ClosedRay _ _ _ => unfold ClosedRay in H; stepOpenRayClockwise1 H
	| forall M : Point, Clockwise ?D ?E M -> Clockwise ?D ?F M => fold (EquiOriented D E D F) in H; stepOpenRayClockwise1 H
	| forall M : Point, Clockwise ?D ?E M -> Clockwise ?F ?G M => fold (EquiOriented D E F G) in H; stepEquiOrientedClockwise1 H
	| EquiOriented _ _ _ _ => stepEquiOrientedClockwise1 H
	| Between _ _ _  => stepBetweenClockwise3 H
	| Segment ?X ?Y ?Z => let Hyp := fresh in (assert (Hyp : Between X Z Y); 
				[apply (SegmentBetween X Z Y H); try immediate3 | stepBetweenClockwise3 Hyp])

	| Clockwise A ?D ?E => apply (OpenRaysClockwise A D E B C H); try immediate3
	| Clockwise ?E A ?D => apply (OpenRaysClockwise A D E B C (ClockwiseBCA _ _ _ H)); try immediate3
	| Clockwise ?D ?E A => apply (OpenRaysClockwise A D E B C (ClockwiseCAB _ _ _ H)); try immediate3
	| Clockwise B ?D ?E => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A H); try immediate3
	| Clockwise ?E B ?D => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A (ClockwiseBCA _ _ _ H)); try immediate3
	| Clockwise ?D ?E B => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A (ClockwiseCAB _ _ _ H)); try immediate3
	| Clockwise C ?D ?E => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B H); try immediate3
	| Clockwise ?E C ?D => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B (ClockwiseBCA _ _ _ H)); try immediate3
	| Clockwise ?D ?E C => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B (ClockwiseCAB _ _ _ H)); try immediate3

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate3
end.

Ltac stepBetween3 A B D H := match type of H with

	| Segment A D B => apply SegmentBetween; try immediate3
	| Segment D A B => apply BetweenSym; apply SegmentBetween; try immediate3
	| OpenRay B ?C D => apply (OpenRayBetween A B C D H); try immediate3
	| ClosedRay B D ?C => apply (OpenRayBetween A B C D); try immediate3
	| OpenRay B D ?C => apply (OpenRayBetween A B C D H); try immediate3
	| ClosedRay B ?C D => apply (OpenRayBetween A B C D); try immediate3
	| EquiOriented B ?C B D => apply (OpenRayBetween A B C D); try immediate3
	| OpenRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate3
	| ClosedRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate3
	| OpenRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate3
	| ClosedRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate3
	| EquiOriented B ?C B A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate3

	| Between A B ?C => apply (OpenRayBetween A B C D); try immediate3
	| Between ?C B A => apply (OpenRayBetween A B C D); try immediate3
	| Between D B ?C => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3
	| Between ?C B D => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3
	| Segment A ?C B => apply (OpenRayBetween A B C D); try immediate3
	| Segment ?C A B => apply (OpenRayBetween A B C D); try immediate3
	| Segment D ?C B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3
	| Segment ?C D B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3

	| Between A ?C B => apply (BetweenTransACD A C B D); try immediate3
	| Between B ?C A => apply (BetweenTransACD A C B D); try immediate3
	| Between B ?C D => apply BetweenSym; apply (BetweenTransACD D C B A); try immediate3
	| Between D ?C B => apply BetweenSym; apply (BetweenTransACD D C B A); try immediate3
	| Between ?C A B => apply (BetweenTransBCD C A B D); try immediate3
	| Between B A ?C => apply (BetweenTransBCD C A B D); try immediate3
	| Between ?C D B => apply BetweenSym; apply (BetweenTransBCD C D B A); try immediate3
	| Between B D  ?C => apply BetweenSym; apply (BetweenTransBCD C D B A); try immediate3

	| Segment A B ?C => apply (BetweenTransACD A C B D); try immediate3
	| Segment B A ?C => apply (BetweenTransACD A C B D); try immediate3
	| Segment B D ?C => apply BetweenSym; apply (BetweenTransACD D C B A); try immediate3
	| Segment D B ?C => apply BetweenSym; apply (BetweenTransACD D C B A); try immediate3
	| Segment ?C B A => apply (BetweenTransBCD C A B D); try immediate3
	| Segment B ?C A => apply (BetweenTransBCD C A B D); try immediate3
	| Segment ?C B D => apply BetweenSym; apply (BetweenTransBCD C D B A); try immediate3
	| Segment B ?C D => apply BetweenSym; apply (BetweenTransBCD C D B A); try immediate3

	| Between ?E B ?F => apply (OpenRaysBetween B E F A D H); try immediate3

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate3
end.

Ltac stepEquiOrientedCollinear3 A B C D H := match goal with
	| |- Collinear A B C => apply (EquiOrientedCollinearCollinearABC A B C D H); try solve [intuition]
	| |- Collinear A C B => apply CollinearACB; apply (EquiOrientedCollinearCollinearABC A B C D H); try solve [intuition]
	| |- Collinear B A C => apply CollinearBAC; apply (EquiOrientedCollinearCollinearABC A B C D H); try solve [intuition]
	| |- Collinear B C A => apply CollinearBCA; apply (EquiOrientedCollinearCollinearABC A B C D H); try solve [intuition]
	| |- Collinear C A B => apply CollinearCAB; apply (EquiOrientedCollinearCollinearABC A B C D H); try solve [intuition]
	| |- Collinear C B A => apply CollinearCBA; apply (EquiOrientedCollinearCollinearABC A B C D H); try solve [intuition]

	| |- Collinear A B D => apply (EquiOrientedCollinearCollinearABD A B C D H); try solve [intuition]
	| |- Collinear A D B => apply CollinearACB; apply (EquiOrientedCollinearCollinearABD A B C D H); try solve [intuition]
	| |- Collinear B A D => apply CollinearBAC; apply (EquiOrientedCollinearCollinearABD A B C D H); try solve [intuition]
	| |- Collinear B D A => apply CollinearBCA; apply (EquiOrientedCollinearCollinearABD A B C D H); try solve [intuition]
	| |- Collinear D A B => apply CollinearCAB; apply (EquiOrientedCollinearCollinearABD A B C D H); try solve [intuition]
	| |- Collinear D B A => apply CollinearCBA; apply (EquiOrientedCollinearCollinearABD A B C D H); try solve [intuition]

	| |- Collinear A C D => apply (EquiOrientedCollinearCollinearACD A B C D H); try solve [intuition]
	| |- Collinear A D C => apply CollinearACB; apply (EquiOrientedCollinearCollinearACD A B C D H); try solve [intuition]
	| |- Collinear C A D => apply CollinearBAC; apply (EquiOrientedCollinearCollinearACD A B C D H); try solve [intuition]
	| |- Collinear C D A => apply CollinearBCA; apply (EquiOrientedCollinearCollinearACD A B C D H); try solve [intuition]
	| |- Collinear D A C => apply CollinearCAB; apply (EquiOrientedCollinearCollinearACD A B C D H); try solve [intuition]
	| |- Collinear D C A => apply CollinearCBA; apply (EquiOrientedCollinearCollinearACD A B C D H); try solve [intuition]

	| |- Collinear B C D => apply (EquiOrientedCollinearCollinearBCD A B C D H); try solve [intuition]
	| |- Collinear B D C => apply CollinearACB; apply (EquiOrientedCollinearCollinearBCD A B C D H); try solve [intuition]
	| |- Collinear C B D => apply CollinearBAC; apply (EquiOrientedCollinearCollinearBCD A B C D H); try solve [intuition]
	| |- Collinear C D B => apply CollinearBCA; apply (EquiOrientedCollinearCollinearBCD A B C D H); try solve [intuition]
	| |- Collinear D B C => apply CollinearCAB; apply (EquiOrientedCollinearCollinearBCD A B C D H); try solve [intuition]
	| |- Collinear D C B => apply CollinearCBA; apply (EquiOrientedCollinearCollinearBCD A B C D H); try solve [intuition]
end.												

Ltac stepCollinear3 H := match type of H with

	| Line => apply (OnLine3 H); try immediate3

	| OnLine (Ruler _ _ _) _ =>  unfold OnLine in H; simpl in H; immCollinear2
	| Diameter (Ruler _ _ _) _ =>  unfold Diameter, OnLine in H; simpl in H; immCollinear2
	| OnLine ?l _ =>  unfold l, OnLine in H; simpl in H; immCollinear2
	| Diameter ?l _ =>  unfold l, Diameter, OnLine in H; simpl in H; immCollinear2
	| EquiOriented ?A ?B ?C ?D => stepEquiOrientedCollinear3 A B C D H

	| Collinear ?A ?B ?C => match goal with
		| Hab : A <> B |- Collinear A C ?D => apply (CollinearTrans A B C D Hab H); try immediate3
		| Hba : B <> A |- Collinear A C ?D => apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate3
		| Hab : A <> B |- Collinear C ?D A => apply CollinearBCA; apply (CollinearTrans A B C D Hab H); try immediate3
		| Hba : B <> A |- Collinear C ?D A => apply CollinearBCA; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate3
		| Hab : A <> B |- Collinear ?D A C => apply CollinearCAB ; apply (CollinearTrans A B C D Hab H); try immediate3
		| Hba : B <> A |- Collinear ?D A C => apply CollinearCAB ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate3
		| Hab : A <> B |- Collinear C A ?D => apply CollinearBAC ; apply (CollinearTrans A B C D Hab H); try immediate3
		| Hba : B <> A |- Collinear C A ?D => apply CollinearBAC ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate3
		| Hab : A <> B |- Collinear ?D C A => apply CollinearCBA; apply (CollinearTrans A B C D Hab H); try immediate3
		| Hba : B <> A |- Collinear ?D C A => apply CollinearCBA; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate3
		| Hab : A <> B |- Collinear A ?D C => apply CollinearACB ; apply (CollinearTrans A B C D Hab H); try immediate3
		| Hba : B <> A |- Collinear A ?D C => apply CollinearACB ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate3
		| Hab : B <> A |- Collinear B C ?D => apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate3
		| Hba : A <> B |- Collinear B C ?D => apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate3
		| Hab : B <> A |- Collinear C ?D B => apply CollinearBCA; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate3
		| Hba : A <> B |- Collinear C ?D B => apply CollinearBCA; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate3
		| Hab : B <> A |- Collinear ?D B C => apply CollinearCAB ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate3
		| Hba : A <> B |- Collinear ?D B C => apply CollinearCAB ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate3
		| Hab : B <> A |- Collinear C B ?D => apply CollinearBAC ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate3
		| Hba : A <> B |- Collinear C B ?D => apply CollinearBAC ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate3
		| Hab : B <> A |- Collinear ?D C B => apply CollinearCBA; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate3
		| Hba : A <> B |- Collinear ?D C B => apply CollinearCBA; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate3
		| Hab : B <> A |- Collinear B ?D C => apply CollinearACB ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate3
		| Hba : A <> B |- Collinear B ?D C => apply CollinearACB ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate3
		| Hab : C <> B |- Collinear C A ?D => apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate3
		| Hba : B <> C |- Collinear C A ?D => apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate3
		| Hab : C <> B |- Collinear A ?D C => apply CollinearBCA; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate3
		| Hba : B <> C |- Collinear A ?D C => apply CollinearBCA; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate3
		| Hab : C <> B |- Collinear ?D C A => apply CollinearCAB ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate3
		| Hba : B <> C |- Collinear ?D C A => apply CollinearCAB ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate3
		| Hab : C <> B |- Collinear A C ?D => apply CollinearBAC ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate3
		| Hba : B <> C |- Collinear A C ?D => apply CollinearBAC ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate3
		| Hab : C <> B |- Collinear ?D A C => apply CollinearCBA; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate3
		| Hba : B <> C |- Collinear ?D A C => apply CollinearCBA; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate3
		| Hab : C <> B |- Collinear C ?D A => apply CollinearACB ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate3
		| Hba : B <> C |- Collinear C ?D A => apply CollinearACB ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate3
		| Hab : B <> C |- Collinear B A ?D => apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate3
		| Hba : C <> B |- Collinear B A ?D => apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate3
		| Hab : B <> C |- Collinear A ?D B => apply CollinearBCA; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate3
		| Hba : C <> B |- Collinear A ?D B => apply CollinearBCA; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate3
		| Hab : B <> C |- Collinear ?D B A => apply CollinearCAB ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate3
		| Hba : C <> B |- Collinear ?D B A => apply CollinearCAB ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate3
		| Hab : B <> C |- Collinear A B ?D => apply CollinearBAC ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate3
		| Hba : C <> B |- Collinear A B ?D => apply CollinearBAC ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate3
		| Hab : B <> C |- Collinear ?D A B => apply CollinearCBA; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate3
		| Hba : C <> B |- Collinear ?D A B => apply CollinearCBA; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate3
		| Hab : B <> C |- Collinear B ?D A => apply CollinearACB ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate3
		| Hba : C <> B |- Collinear B ?D A => apply CollinearACB ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate3
		| Hab : A <> C |- Collinear A B ?D => apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate3
		| Hba : C <> A |- Collinear A B ?D => apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate3
		| Hab : A <> C |- Collinear B ?D A => apply CollinearBCA; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate3
		| Hba : C <> A |- Collinear B ?D A => apply CollinearBCA; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate3
		| Hab : A <> C |- Collinear ?D A B => apply CollinearCAB ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate3
		| Hba : C <> A |- Collinear ?D A B => apply CollinearCAB ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate3
		| Hab : A <> C |- Collinear B A ?D => apply CollinearBAC ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate3
		| Hba : C <> A |- Collinear B A ?D => apply CollinearBAC ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate3
		| Hab : A <> C |- Collinear ?D B A => apply CollinearCBA; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate3
		| Hba : C <> A |- Collinear ?D B A => apply CollinearCBA; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate3
		| Hab : A <> C |- Collinear A ?D B => apply CollinearACB ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate3
		| Hba : C <> A |- Collinear A ?D B => apply CollinearACB ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate3
		| Hab : C <> A |- Collinear C B ?D => apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate3
		| Hba : A <> C |- Collinear C B ?D => apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate3
		| Hab : C <> A |- Collinear B ?D C => apply CollinearBCA; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate3
		| Hba : A <> C |- Collinear B ?D C => apply CollinearBCA; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate3
		| Hab : C <> A |- Collinear ?D C B => apply CollinearCAB ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate3
		| Hba : A <> C |- Collinear ?D C B => apply CollinearCAB ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate3
		| Hab : C <> A |- Collinear B C ?D => apply CollinearBAC ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate3
		| Hba : A <> C |- Collinear B C ?D => apply CollinearBAC ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate3
		| Hab : C <> A |- Collinear ?D B C => apply CollinearCBA; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate3
		| Hba : A <> C |- Collinear ?D B C => apply CollinearCBA; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate3
		| Hab : C <> A |- Collinear C ?D B => apply CollinearACB ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate3
		| Hba : A <> C |- Collinear C ?D B => apply CollinearACB ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate3
		end

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate3
end.

Ltac byDefEqPoint3 := match goal with
	| |- ?X = ?X => apply refl_equal

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); try immediate3
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M);try immediate3
end.

Ltac stepEq3 X Y H  := match type of H with
	| Point => apply trans_eq with (y:=H); unfold H; byDefEqPoint3

	| OnCircle ?c ?A  => simplCircleHyp2 H; try solveDist2

	| SecantCircles ?c1 ?c2 => apply (EqPointsIntersectionCircles c1 c2 H); try immediate3

	| X = ?Z => rewrite H; try solveEq3
	| Y = ?Z => rewrite H; try solveEq3
	| ?Z = X => rewrite <- H; try solveEq3
	| ?Z = Y => rewrite <- H; try solveEq3

	| ?Z = ?T => first 
			[let Hyp := fresh in (assert (Hyp : X=Z); [solveEq3 | rewrite Hyp; clear Hyp; rewrite H; try solveEq3]) |
			let Hyp := fresh in (assert (Hyp : Y=Z); [solveEq3 | rewrite Hyp ; clear Hyp; rewrite H; try solveEq3]) |
			let Hyp := fresh in (assert (Hyp : X=T); [solveEq3 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq3]) |
			let Hyp := fresh in (assert (Hyp : Y=T); [solveEq3 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq3])]
end.

Ltac stepDistanceLt3 H := match type of H with
	| Distance ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLt (Distance A B) _ => rewrite H
		| |- DistanceLt (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt _ (Distance A B) => rewrite H
		| |- DistanceLt _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt (Distance C D) _ => rewrite <- H
		| |- DistanceLt (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLt _ (Distance C D) => rewrite <- H
		| |- DistanceLt _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| DistancePlus ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLt (DistancePlus A B) _ => rewrite H
		| |- DistanceLt (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt _ (DistancePlus A B) => rewrite H
		| |- DistanceLt _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt (Distance C D) _ => rewrite <- H
		| |- DistanceLt (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLt _ (Distance C D) => rewrite <- H
		| |- DistanceLt _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| Distance ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLt (Distance A B) _ => rewrite H
		| |- DistanceLt (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt _ (Distance A B) => rewrite H
		| |- DistanceLt _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLt (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLt _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLt _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistancePlus ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLt (DistancePlus A B) _ => rewrite H
		| |- DistanceLt (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt _ (DistancePlus A B) => rewrite H
		| |- DistanceLt _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLt (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLt _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLt _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistanceTimes ?n ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLt (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLt (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLt _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt (Distance C D) _ => rewrite <- H
		| |- DistanceLt (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLt _ (Distance C D) => rewrite <- H
		| |- DistanceLt _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| Distance ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLt (Distance A B) _ => rewrite H
		| |- DistanceLt (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt _ (Distance A B) => rewrite H
		| |- DistanceLt _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLt (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLt _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLt _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
	| DistanceTimes ?n ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLt (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLt (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLt _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLt (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLt _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLt _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistancePlus ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLt (DistancePlus A B) _ => rewrite H
		| |- DistanceLt (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt _ (DistancePlus A B) => rewrite H
		| |- DistanceLt _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLt (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLt _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLt _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
	| DistanceTimes ?n ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLt (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLt (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLt _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLt (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLt _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLt _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
end.

Ltac step3 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance2 H
	| |- _ = DistancePlus _ _  => stepEqDistance2 H

	| |- DistanceTimes _ _ _ = _ =>  stepEqDistance2 H
	| |- _ = DistanceTimes _ _ _ =>  stepEqDistance2 H

	| |- Distance _ _ = _ => stepEqDistance2 H
	| |- _ = Distance _ _ => stepEqDistance2 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |- ?A = ?B => stepEq3 A B H
	| |- ?A <> ?B => stepDistinct3 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct3 A B H

	| |- Collinear _ _ _  => stepCollinear3 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented1 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay1 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay1 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise3 A B C H
	| |- Between ?A ?B ?D => stepBetween3 A B D H
	| |- Segment ?A ?B ?C  => stepSegment1 A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec2 A B C D E F H
end.

Ltac setClockwise3 A B C := match goal with
	| H : A <> B |- _ => pose (C := ExistsClockwise A B H) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B H);
					fold C in Hyp)
	| H : B <> A |- _ => pose (C := ExistsClockwise A B (sym_not_eq H)) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
					fold C in Hyp)
	| H : A = B -> False |- _ => pose (C := ExistsClockwise A B H) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B H);
					fold C in Hyp)
	| H : B = A -> False |- _ => pose (C := ExistsClockwise A B  (sym_not_eq H)) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
					fold C in Hyp)
	| _ => let H := fresh in (
			assert (H : A <> B);
			[ try immDistinct3 | pose (C := ExistsClockwise A B H) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B H);
					fold C in Hyp) ] )
end.

Ltac  byApartCases3 A B C := match goal with
	| H : A <> B |- _ => destruct (Apart A B C H)
	| H : B <> A |- _ => destruct (Apart A B C  (sym_not_eq H)) 
	| H : A = B -> False |- _ => destruct (Apart A B C H)
	| H : B = A -> False |- _ => destruct (Apart A B C  (sym_not_eq H)) 
	| _ => let H := fresh in (
			assert (H : A <> B);
			[ try immDistinct1 | destruct (Apart A B C H)])

end.

Ltac since3 txt := assert txt; try immediate3.

Ltac from3 H txt := assert txt; [(step3 H; try immediate3) |  try immediate3].

Ltac as3 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate3 | (step3 Hyp; try immediate3)]).

Ltac setIntersectionCircles3 c1 c2 M := match goal with
	| H : SecantCircles c1 c2 |- _ => pose (M := IntersectionCirclesPoint c1 c2 H);
			let Hyp1 := fresh in (
				assert (Hyp1 := OnCircle1IntersectionCirclesPoint c1 c2 H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircle2IntersectionCirclesPoint c1 c2 H);
					let Hyp3 := fresh in (
						assert (Hyp3 := NotClockwiseIntersectionCirclesPoint c1 c2 H);
						fold M in Hyp1, Hyp2, Hyp3; simpl in Hyp1, Hyp2, Hyp3)))
	| H : SecantCircles c2 c1 |- _ => pose (M := IntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
			let Hyp1 := fresh in (
				assert (Hyp1 := OnCircle1IntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircle2IntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
					let Hyp3 := fresh in (
						assert (Hyp3 := NotClockwiseIntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
						fold M in Hyp1, Hyp2, Hyp3; simpl in Hyp1, Hyp2, Hyp3)))
	| _ => let H := fresh in (
		assert (H : SecantCircles c1 c2);
		[(split; try immediate3) |
			pose (M := IntersectionCirclesPoint c1 c2 H);
			let Hyp1 := fresh in (
				assert (Hyp1 := OnCircle1IntersectionCirclesPoint c1 c2 H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircle2IntersectionCirclesPoint c1 c2 H);
					let Hyp3 := fresh in (
						assert (Hyp3 := NotClockwiseIntersectionCirclesPoint c1 c2 H);
						fold M in Hyp1, Hyp2, Hyp3; simpl in Hyp1, Hyp2, Hyp3)))])
end.
