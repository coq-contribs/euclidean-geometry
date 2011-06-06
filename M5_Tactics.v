
Ltac immEqLine12 := match goal with 
	| |- EqLine ?d ?d  => apply EqLineRefl
	| H : EqLine ?d1 ?d2 |- EqLine ?d2 ?d1 => apply (EqLineSym d1 d2 H)
	| H : forall M : Point, OnLine ?d2 M -> OnLine ?d1 M |- EqLine ?d1 ?d2 => apply (OnLineEqLine d1 d2 H)
	| H : forall M : Point, OnLine ?d1 M -> OnLine ?d2 M |- EqLine ?d1 ?d2 => apply EqLineSym; apply (OnLineEqLine d2 d1 H)
	| |- EqLine (Ruler ?A ?B ?H1) (Ruler ?A ?B ?H2) => apply (EqLineId A B H1 H2)
	| |- EqLine (Ruler ?A ?B ?H1) (Ruler ?B ?A ?H2) => apply (EqLineOpp A B H1 H2)
end.

Ltac immNotEqLine12 := match goal with 
	| H : SecantLines ?d1 ?d2 |- ~EqLine ?d1 ?d2 => apply (SecantNotEqLines d1 d2 H)
end.

Ltac immParallelLines12 := match goal with 
	| |- ParallelLines ?d ?d  => apply ParallelLinesRefl
	| H : ParallelLines ?d1 ?d2 |- ParallelLines ?d2 ?d1 => apply (ParallelLinesSym d1 d2 H)
	| H : EqLine ?d1 ?d2 |- ParallelLines ?d1 ?d2 => apply (EqParallelLine d1 d2 H)
	| H : EqLine ?d1 ?d2 |- ParallelLines ?d2 ?d1 => apply ParallelLinesSym; apply (EqParallelLine d1 d2 H)
	
	| _ => unfold ParallelLines; immediate11
end.

Ltac immSecantLines12 := match goal with 
	| H : SecantLines ?d1 ?d2 |- SecantLines ?d2 ?d1 => apply (SecantLinesSym d1 d2 H)
	| H : Perpendicular ?d1 ?d2 |- SecantLines ?d1 ?d2 => apply (PerpendicularSecant d1 d2 H)

	| _ => unfold SecantLines; immediate11
end.

Ltac immNotSecantLines12 := match goal with 
	| H : EqLine ?d1 ?d2 |- ~SecantLines ?d1 ?d2 => apply (EqNotSecantLines d1 d2 H)

	| _ => let Hyp := fresh in (intro Hyp; elim Hyp; immParallelLines12)
end.

Ltac immPerpendicular12 := match goal with 
	| H : Perpendicular ?d1 ?d2 |- Perpendicular ?d2 ?d1 => apply (PerpendicularSym d1 d2 H)

	| |- Perpendicular (Ruler ?A ?B ?Hab) (MidLine ?A ?B ?Hab) => apply (PerpendicularMidLine A B Hab)
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?A ?B ?Hab) => apply PerpendicularSym; apply (PerpendicularMidLine A B Hab)

	| |- Perpendicular (Ruler ?A ?B ?Hab') (MidLine ?A ?B ?Hab) => apply (EqEqPerpendicular (Ruler A B Hab) (Ruler A B Hab') (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineId A B Hab Hab') |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?A ?B ?Hab') => apply PerpendicularSym; apply (EqEqPerpendicular (Ruler A B Hab) (Ruler A B Hab') (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineId A B Hab Hab') |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]

	| |- Perpendicular (Ruler ?B ?A ?Hba) (MidLine ?A ?B ?Hab) => apply (EqEqPerpendicular (Ruler A B Hab) (Ruler B A Hba) (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineOpp A B Hab Hba) |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?B ?A ?Hba) => apply PerpendicularSym; apply (EqEqPerpendicular (Ruler A B Hab) (Ruler B A Hba) (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineOpp A B Hab Hba) |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]

end.

Ltac immOnLine12 := match goal with
	| H : OnLine ?d ?A |- OnLine ?d ?A => exact H
	| |- OnLine ?d (LineA ?d) => destruct d; simpl; immediate8
	| |- OnLine ?d (LineB ?d) => destruct d; simpl; immediate8

	| |- OnLine ?d (InterLinesPoint ?d _ _) => apply OnLine1InterLinesPoint
	| |- OnLine ?d (InterLinesPoint _ ?d _) => apply OnLine2InterLinesPoint
	| |- OnLine ?d (InterDiameterPoint ?d _ _) => apply OnLineInterDiameterPoint
	| |- OnLine ?d (SecondInterDiameterPoint ?d _ _) => apply OnLineSecondInterDiameterPoint

	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?A ?B ?H) => apply MidPointOnMidLine
	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?A ?B ?H') => rewrite (MidPointRefl A B H' H); apply MidPointOnMidLine
	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?B ?A ?H') =>  rewrite (MidPointSym B A H' H); apply MidPointOnMidLine

	| |- OnLine (MidLine Uu uU DistinctUuuU) Vv => apply OnMidLineVv
	| |- OnLine (MidLine Uu uU DistinctUuuU) RightAngle => unfold RightAngle; apply OnMidLineVv

	| |- OnLine (MidLine ?A ?B ?H) ?M => apply EqDistanceOnMidLine; solveDist9

	| |- OnLine ?d (PerpendicularPoint ?d _ _) => apply PerpendicularPointOnLine1
	| |- OnLine ?d (PerpendicularPoint _ ?d _) => apply PerpendicularPointOnLine2

	| |- OnLine (Ruler _ _ _) _ => simpl; immediate8
	| |- OnLine ?d _ => unfold d; simpl; immediate8
end.

Ltac solveEq12 := match goal with
	| |- Uu = InterDiameterPoint lineOoUu uCircle _ => apply InterPointLineOoUuuCircle
	| |- InterDiameterPoint lineOoUu uCircle _  = Uu => apply sym_eq; apply InterPointLineOoUuuCircle

	| |- uU = SecondInterDiameterPoint lineOoUu uCircle _ => apply SecondInterPointLineOoUuuCircle
	| |- SecondInterDiameterPoint lineOoUu uCircle _  = uU => apply sym_eq; apply SecondInterPointLineOoUuuCircle

	| |- ?X = ?X => apply refl_equal
	| H : ?X = ?Y |- ?X = ?Y => exact H
	| H : ?Y = ?X |- ?X = ?Y => rewrite H; apply refl_equal

	| |- Graduation 0 ?A ?B ?Hab = ?A => apply Graduation0
	| |- ?A = Graduation 0 ?A ?B ?Hab => apply sym_eq; apply Graduation0
	| |- Graduation 1 ?A ?B ?Hab = ?B => apply Graduation1
	| |- ?B = Graduation 1 ?A ?B ?Hab => apply sym_eq; apply Graduation1

	| |- Graduation (S ?n) ?A ?B ?Hab = AddSegmentPoint ?A ?B (Graduation ?n ?A ?B ?Hab) ?A ?B ?Hab (CollinearGraduation ?n ?A ?B ?Hab) => apply GraduationSn
	| |- AddSegmentPoint ?A ?B (Graduation ?n ?A ?B ?Hab) ?A ?B ?Hab (CollinearGraduation ?n ?A ?B ?Hab) = Graduation (S ?n) ?A ?B ?Hab => apply sym_eq; apply GraduationSn

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle5 | immOnCircle5 | immNotClockwise3]
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle5 | immOnCircle5 | immNotClockwise3]

	| |- ?M = InterLinesPoint ?l1 ?l2 ?H => apply (UniqueInterLinesPoint l1 l2 H M); immOnLine5
	| |- InterLinesPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueInterLinesPoint l1 l2 H M); immOnLine5

	| |- ?M = NotEquiDirectedInterPoint ?l1 ?l2 ?H => apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); immCollinear5
	| |- NotEquiDirectedInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); immCollinear5

	| |- ?M = FourPointsInterPoint ?l1 ?l2 ?H => apply (UniqueFourPointsInterPoint l1 l2 H M); immCollinear5
	| |- FourPointsInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueFourPointsInterPoint l1 l2 H M); immCollinear5

	| |- ?M = InterDiameterPoint ?l ?c ?H => apply (UniqueInterDiameterPoint l c H M); [immEquiOriented5 | immOnCircle5]
	| |- InterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueInterDiameterPoint l c H M);  [immEquiOriented5 | immOnCircle5]

	| |- ?M = SecondInterDiameterPoint ?l ?c ?H => apply (UniqueSecondInterDiameterPoint l c H M); [immEquiOriented5 | immOnCircle5]
	| |- SecondInterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueSecondInterDiameterPoint l c H M);  [immEquiOriented5 | immOnCircle5]

	| |- ?M = AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 => apply (UniqueAddSegmentPoint A B C D E H H0 M); [immEquiOriented5 | solveDistance7]
	| |- AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 = ?M => apply sym_eq; apply (UniqueAddSegmentPoint A B C D E H H0 M); [immEquiOriented5 | solveDistance7]

	| |- ?M = MarkSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueMarkSegmentPoint A B C D H M); [immClosedRay5 | solveDistance7]
	| |- MarkSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueMarkSegmentPoint A B C D H M); [immClosedRay5 | solveDistance7]

	| |- ?M = OppSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueOppSegmentPoint A B C D H M); [immSegment5 | solveDistance7]
	| |- OppSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueOppSegmentPoint A B C D H M); [immSegment5 | solveDistance7]

	| |- ?M = SymmetricPoint ?A ?B ?H => apply (UniqueSymmetricPoint A B H M); [immBetween5 | solveDistance7]
	| |- SymmetricPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueSymmetricPoint A B H M); [immBetween5 | solveDistance7]

	| |- ?M = PerpendicularPoint ?d1 ?d2 ?Hp => apply (UniquePerpendicularPoint M d1 d2 Hp); immOnLine12
	| |- PerpendicularPoint ?d1 ?d2 ?Hp = ?M => apply sym_eq; apply (UniquePerpendicularPoint M d1 d2 Hp); immOnLine12

	| H1 : IsAngle ?alpha, H2 : IsAngle ?beta |- ?alpha = ?beta => apply (EqAngle alpha beta H1 H2); solveDistance6

	| |- Oo = MidPoint Uu uU DistinctUuuU => exact MidPointUuuUOo
	| |- Oo = MidPoint Uu uU ?H => rewrite (MidPointRefl Uu uU H DistinctUuuU); exact MidPointUuuUOo
	| |- MidPoint Uu uU DistinctUuuU = Oo => apply sym_eq; exact MidPointUuuUOo
	| |- MidPoint Uu uU ?H = Oo => apply sym_eq;  rewrite (MidPointRefl Uu uU H DistinctUuuU); exact MidPointUuuUOo
	| |- Oo = MidPoint uU Uu ?H =>  rewrite (MidPointSym uU Uu H DistinctUuuU); exact MidPointUuuUOo
	| |- MidPoint uU Uu ?H = Oo => apply sym_eq;  rewrite (MidPointSym uU Uu H DistinctUuuU); exact MidPointUuuUOo

	| |- MidPoint ?A ?B _  = MidPoint ?A ?B _ => apply MidPointRefl
	| |- MidPoint ?A ?B _  = MidPoint ?B ?A _ => apply MidPointSym
	| |- ?M = MidPoint ?A ?B ?H => apply (UniqueMidPoint A B H M); [immCollinear9 | solveDistance7]
	| |- MidPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueMidPoint A B H M); [immCollinear9 | solveDistance7]

	| |- ?A = ?B => match type of A with
			| Point => let H := fresh in (assert (H : Distance A B = Oo); [solveDistance7 | apply (NullDistanceEq A B H)])
			end

	| |- ?X = _ => unfold X; solveEq7
	| |- _ = ?Y => unfold Y; solveEq7
end.

Ltac immediate12 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate12
	| |- ?A \/ ?B => (left; immediate12)  || (right; immediate12)

	| |- DistancePlus _ _ = _ => solveDistance11
	| |- _ = DistancePlus _ _ => solveDistance11

	| |- DistanceTimes _ _ _ = _ => solveDistance11
	| |- _ = DistanceTimes _ _ _ => solveDistance11

	| |- Distance _ _ = _ => solveDistance11
	| |- _ = Distance _ _ => solveDistance11

	| |- IsDistance ?d => immIsDistance2 d

	| |- Supplementary _ _ = _ => solveSupplementary10 || (apply SupplementarySym; solveSupplementary10)
	| |- _ = Supplementary _ _ => solveSupplementary10 || (apply SupplementarySym; solveSupplementary10)

	| |-  Supplement _ _ _ _ _ _ => immSupplement11
	| |-  OpposedAngles _ _ _ _ _ =>  apply OpposedAngleDef; immBetween8 

	| |- Angle _ _ _ _ _ = _ => solveAngle10
	| |-  _ = Angle _ _ _ _ _ => solveAngle10

	| |- CongruentAngle _ _ _ _ _ _ => immCongruentAngle11
	| |- NullAngle _ _ _ => immNullAngle6
	| |- ElongatedAngle _ _ _ => immElongatedAngle6
	| |- RightAngle _ _ _ => immRightAngle10
	| |- ~NullAngle _ _ _ => immNotNullAngle10
	| |- ~ElongatedAngle _ _ _ => immNotElongatedAngle10
	| |- ~RightAngle _ _ _ => immNotRightAngle10

	| |- IsAngle _ => immIsAngle10

	| |- _ = _ => solveEq12
	| |- _ <> _ => immDistinct11
	| |- ?A = ?B -> False => fold(A <> B); immDistinct11

	| |- Clockwise _ _ _ => immClockwise11
	| |- ~Clockwise _ _ _  => immNotClockwise11
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise11

	| |- Collinear _ _ _ => immCollinear9
	| |- ~Collinear _ _ _  => immNotCollinear10
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear10

	| |- EquiOriented _ _ _ _ => immEquiOriented11
	| |- OpenRay _ _ _ => immOpenRay6
	| |- ClosedRay _ _ _ => immClosedRay6
	| |- Between _ _ _ => immBetween11
	| |- Segment _ _ _ => immSegment11

	| |- EquiDirected _ _ _ _ => immEquiDirected11
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected4
	| |- EquiDirected ?A ?B ?C ?D  -> False => fold (~EquiDirected A B C D); immNotEquiDirected4

	| |- DistanceLe _ _ => immDistanceLe2
	| |- DistanceLt _ _ => immDistanceLt3

	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality3
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec3

	| |- Diameter _ _ => immDiameter2
	| |- SecantLines _ _ => immSecantLines4

	| |- OnCircle _ _ => immOnCircle6
	| |- OnLine _ _ => immOnLine12

	| |- TStrict _ => immTStrict7
	| |- Isosceles1 ?t => unfold t; immIsoscelesOne7
	| |- Isosceles1 (Tr _ _ _) => immIsoscelesOne7
	| |- Isosceles2 ?t => unfold t; immIsoscelesTwo7
	| |- Isosceles2 (Tr _ _ _) => immIsoscelesTwo7
	| |- Isosceles3 ?t => unfold t; immIsoscelesThree7
	| |- Isosceles3 (Tr _ _ _) => immIsoscelesThree7
	| |- Equilateral ?t => unfold t; immEquilateral9
	| |- Equilateral (Tr _ _ _) => immEquilateral9

	| |- TCongruent _ _ => immTCongruent11

	| |- Parallelogramm _ _ _ _ => immParallelogramm11
	| |- StrictParallelogramm _ _ _ _ => immStrictParallelogramm11

	| |- EqLine _ _ => immEqLine12
	| |- ~EqLine _ _ => immNotEqLine12
	| |- EqLine ?d1 ?d2  -> False =>  fold (~EqLine d1 d2); immNotEqLine12
	| |- ParallelLines _ _ => immParallelLines12
	| |- SecantLines _ _ => immSecantLines12
	| |- ~SecantLines _ _ => immNotSecantLines12
	| |- SecantLines ?d1 ?d2  -> False =>  fold (~SecantLines d1 d2); immNotSecantLines12
	| |- Perpendicular _ _ => immPerpendicular12
end.

Ltac stepDistinct12 A B H := match type of H with

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

	| Line => match goal with
		| Ha : OnLine H A |- _ => apply (OnLineDistinct A B H Ha); try immediate12
		| Hb : OnLine H B  |- _=> apply sym_not_eq;  apply (OnLineDistinct B A H Hb); try immediate12
		| Hna : ~OnLine H A |- _ => apply sym_not_eq;  apply (OnLineDistinct B A H); [try immediate12| apply Hna]
		| Hnb : ~OnLine H B |- _ => apply (OnLineDistinct A B H); [try immediate12 | apply Hnb]
		| _  => apply (OnLineDistinct A B H); try immediate12
	end
end.

Ltac stepOnLine12 d M H := match type of H with
	| Line => unfold H; stepOnLine9
	| EqLine ?d1 d => apply (EqLineOnLine d1 d M H); try immediate12
	| EqLine d ?d2 => apply (EqLineOnLine d2 d M (EqLineSym d d2 H)); try immediate12
	| OnLine ?d1 M => apply (EqLineOnLine d1 d M); [try immediate12 | apply H]

	| Collinear ?A ?B M => apply (OnLineTwoPoints A B M d); try immediate12
	| Collinear ?A M ?B => apply (OnLineTwoPoints A B M d); try immediate12
	| Collinear M ?A ?B => apply (OnLineTwoPoints A B M d); try immediate12
end.

Ltac stepEqLine12 d1 d2 H := match type of H with 
	| Line => apply (EqLineTrans d1 H d2); try immediate12
	| EqLine d1 ?d3  => apply (EqLineTrans d1 d3 d2 H); try immediate12
	| EqLine ?d3 d1  => apply (EqLineTrans d1 d3 d2 (EqLineSym d3 d1 H)); try immediate12
	| EqLine d2 ?d3  => apply (EqLineTrans d1 d3 d2); [try immediate12 | apply (EqLineSym d2 d3 H)]
	| EqLine ?d3 d2  => apply (EqLineTrans d1 d3 d2); [try immediate12 | apply H]
	
	| ?A <> ?B => apply (EqLineTwoPoints A B d1 d2); try immediate12
	| (Point*Point)%type => match H with
		| (?A, ?B) => apply (EqLineTwoPoints A B d1 d2); try immediate12
	end

	| ParallelLines d1 d2  => match goal with
		| Hm : OnLine d1 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate12
		| Hm : OnLine d2 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate12
	end

	| ParallelLines d2 d1  => match goal with
		| Hm : OnLine d1 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate12
		| Hm : OnLine d2 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate12
	end
end.

Ltac stepParallelLines12 d1 d2 H := match type of H with 
	| EqLine d1 ?d3  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1); [try immediate12 | apply (EqLineSym d1 d3 H)]
	| EqLine ?d3 d1  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1); [try immediate12 | apply H]
	| EqLine d2 ?d3  => apply (ParallelEqParallelLine d1 d3 d2); [try immediate12 | apply (EqLineSym d2 d3 H)]
	| EqLine ?d3 d2  => apply (ParallelEqParallelLine d1 d3 d2); [try immediate12 | apply H]
	
	| ParallelLines d1 ?d3  => apply (ParallelEqParallelLine d1 d3 d2 H); try immediate12
	| ParallelLines ?d3 d1  => apply (ParallelEqParallelLine d1 d3 d2 (ParallelLinesSym d3 d1 H)); try immediate12
	| ParallelLines d2 ?d3  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1 H); try immediate12
	| ParallelLines ?d3 d2  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1 (ParallelLinesSym d3 d2 H)); try immediate12
	
	| ParallelLines ?d3 ?d4  => apply (EqEqParallelLine d3 d4 d1 d2); try immediate12
end.

Ltac stepSecantLines12 d1 d2 H := match H with 
	|  ((?A, ?B), (?C, ?D)) => apply (FourPointsSecantLines d1 d2 A B C D); try immediate12

	|  (?A, ?B) => apply (TwoPointsSecantLine d1 d2 A B); try immediate12

	| _ => match type of H with 
		| EqLine ?d3 d1  => apply (EqSecantSecantLines d3 d1 d2 H); try immediate12
		| EqLine d1 ?d3  => apply (EqSecantSecantLines d3 d1 d2 (EqLineSym d1 d3 H)); try immediate12
		| EqLine ?d3 d2  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1 H); try immediate12
		| EqLine d2 ?d3  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1  (EqLineSym d2 d3 H)); try immediate12
	
		| SecantLines ?d3 d2  => apply (EqSecantSecantLines d3 d1 d2); [try immediate12 | apply H]
		| SecantLines d2 ?d3  =>  apply (EqSecantSecantLines d3 d1 d2); [try immediate12 | apply (SecantLinesSym d2 d3 H)]
		| SecantLines ?d3 d1  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1); [try immediate12 | apply H]
		| SecantLines d1 ?d3  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1); [try immediate12 | apply (SecantLinesSym d1 d3 H)]
	
		| SecantLines ?d3 ?d4  => apply (EqEqSecantSecantLines d3 d1 d4 d2); try immediate12
	end
end.

Ltac stepPerpendicular12 d1 d2 H := match H with 
	|  (?A, (?B, ?C)) => apply (PerpRightAngle d1 d2 A B C); try immediate12

	| _ => match type of H with 
		| EqLine ?d3 d1  => apply (EqEqPerpendicular d3 d1 d2 d2); try immediate12
		| EqLine d1 ?d3  => apply (EqEqPerpendicular d3 d1 d2 d2); try immediate12
		| EqLine ?d3 d2  =>  apply (EqEqPerpendicular d1 d1 d3 d2); try immediate12
		| EqLine d2 ?d3  => apply (EqEqPerpendicular d1 d1 d3 d2); try immediate12
	
		| Perpendicular ?d3 d2  => apply (EqEqPerpendicular d3 d1 d2 d2);  try immediate12
		| Perpendicular d2 ?d3  =>  apply (EqEqPerpendicular d3 d1 d2 d2);  try immediate12
		| Perpendicular ?d3 d1  => apply (EqEqPerpendicular d1 d1 d3 d2);  try immediate12
		| Perpendicular d1 ?d3  => apply (EqEqPerpendicular d1 d1 d3 d2); try immediate12
	
		| Perpendicular ?d3 ?d4  => apply (EqEqPerpendicular d3 d1 d4 d2); try immediate12
	end
end.

Ltac stepRightAngle12 A B C H  := match goal with
	| |- RightAngle A (PerpendicularPoint ?l1 ?l2 ?Hp) C => apply (PerpendicularRightAngle l1 l2 Hp A C); try immediate12
	| _ => match type of H with
		| RightAngle ?D ?E ?F => apply (RightOrRight D E F A B C); try immediate10

		| CongruentAngle ?D ?E ?F A B C => apply (CongruentRightAngle D E F A B C); try immediate10
		| CongruentAngle ?D ?E ?F C B A => apply (CongruentRightAngle D E F A B C); try immediate10
		| CongruentAngle A B C ?D ?E ?F => apply (CongruentRightAngle D E F A B C); try immediate10
		| CongruentAngle C B A ?D ?E ?F => apply (CongruentRightAngle D E F A B C); try immediate10
	
		| Supplement ?D ?E ?F A B C => apply (OrSupplementRight D E F A B C); try immediate10
		| Supplement ?D ?E ?F C B A => apply (OrSupplementRight D E F A B C); try immediate10
		| Supplement A B C ?D ?E ?F => apply (OrSupplementRight D E F A B C); try immediate10
		| Supplement C B A ?D ?E ?F => apply (OrSupplementRight D E F A B C); try immediate10
	
		| OnLine (MidLine A ?D ?H) C => apply (OnMidLineEqMidPointRightAngleA A D  B C H); try immediate10
		| OnLine (MidLine ?D A ?H) C => apply (OnMidLineEqMidPointRightAngleB D A  B C H); try immediate10
		| OnLine (MidLine C ?D ?H) A => apply RightAngleSym; apply (OnMidLineEqMidPointRightAngleA C D B A H); try immediate10
		| OnLine (MidLine ?D C ?H) A => apply RightAngleSym; apply (OnMidLineEqMidPointRightAngleB D C B A H); try immediate10
	
		| Perpendicular ?l1 ?l2 => apply (PointsPerpendicularRightAngle A B C l1 l2 H); try immediate12
	end
end.

Ltac byDefEqPoint12 := match goal with
	| |- ?X = ?X => apply refl_equal

	| |- ?M = Vv => apply EqVv; [try solveDistance10 | try immNotClockwise6 | try solveDistance10]	| |- Vv = ?M => apply sym_eq; apply EqVv; [try solveDistance10 | try immNotClockwise6 | try solveDistance10]

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); try immediate5
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M);try immediate5

	| |- ?M = InterLinesPoint ?l1 ?l2 ?H => apply (UniqueInterLinesPoint l1 l2 H M); try immOnLine5
	| |- InterLinesPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueInterLinesPoint l1 l2 H M); try immOnLine5

	| |- ?M = NotEquiDirectedInterPoint ?l1 ?l2 ?H => apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); try immCollinear5
	| |- NotEquiDirectedInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); try immCollinear5

	| |- ?M = FourPointsInterPoint ?l1 ?l2 ?I3 ?I4 ?H1 ?H2  => apply (UniqueFourPointsInterPoint l1 l2 I3 I4 H1 H2 M); try immCollinear5
	| |- FourPointsInterPoint?l1 ?l2 ?I3 ?I4 ?H1 ?H2 = ?M => apply sym_eq; apply (UniqueFourPointsInterPoint l1 l2 I3 I4 H1 H2 M); try immCollinear5

	| |- ?M = InterDiameterPoint ?l ?c ?H => apply (UniqueInterDiameterPoint l c H M); [try immEquiOriented5 | try immOnCircle5]
	| |- InterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueInterDiameterPoint l c H M);  [try immEquiOriented5 | try immOnCircle5]

	| |- ?M = SecondInterDiameterPoint ?l ?c ?H => apply (UniqueSecondInterDiameterPoint l c H M); [try immEquiOriented5 | try immOnCircle5]
	| |- SecondInterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueSecondInterDiameterPoint l c H M);  [try immEquiOriented5 | try immOnCircle5]

	| |- ?M = AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 => apply (UniqueAddSegmentPoint A B C D E H H0 M); [try immEquiOriented5 | try solveDistance5]
	| |- AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 = ?M => apply sym_eq; apply (UniqueAddSegmentPoint A B C D E H H0 M); [try immEquiOriented5 | try solveDistance5]

	| |- ?M = MarkSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueMarkSegmentPoint A B C D H M); [try immClosedRay5 | try solveDistance5]
	| |- MarkSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueMarkSegmentPoint A B C D H M); [try immClosedRay5 | try solveDistance5]

	| |- ?M = OppSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueOppSegmentPoint A B C D H M); [try immSegment5 | try solveDistance5]
	| |- OppSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueOppSegmentPoint A B C D H M); [try immSegment5 | try solveDistance5]

	| |- ?M = SymmetricPoint ?A ?B ?H => apply (UniqueSymmetricPoint A B H M); [try immBetween5 | try solveDistance5]
	| |- SymmetricPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueSymmetricPoint A B H M); [try immBetween5 | try solveDistance5]

	| |- ?M = MidPoint ?A ?B ?H => apply (UniqueMidPoint A B H M); [try immCollinear9 | try solveDistance9]
	| |- MidPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueMidPoint A B H M); [try immCollinear9 | try solveDistance9]


	| |- ?M = PerpendicularPoint ?d1 ?d2 ?Hp => apply (UniquePerpendicularPoint M d1 d2 Hp); try immOnLine12
	| |- PerpendicularPoint ?d1 ?d2 ?Hp = ?M => apply sym_eq; apply (UniquePerpendicularPoint M d1 d2 Hp); try immOnLine12
end.

Ltac stepEq12 X Y H  := match type of H with
	| Point => match goal with
			| |- X = Vv => byDefEqPoint12
			| |- Vv = Y  => byDefEqPoint12
			| |- X = Supplementary H _ => apply SupplementarySym; try immediate8
			| |- Supplementary H _= Y  => apply sym_eq; apply SupplementarySym; try immediate8
			| _ => apply trans_eq with (y:=H); unfold H; byDefEqPoint5
		end

	| OnCircle ?c ?A  => simplCircleHyp2 H; try solveDist2

	| SecantCircles ?c1 ?c2 => apply (EqPointsIntersectionCircles c1 c2 H); try immediate5
	| SecantLines ?l1 ?l2 => apply (EqPointsInterLines l1 l2 H X Y); try immediate5
	| ~EquiDirected ?A ?B ?C ?D => apply (EqPointsNotEquiDirectedInter A B C D X Y H); try immediate5
	| Diameter ?l ?c => apply (EqPointsInterDiameter l c H); try immediate5

	| ~Collinear X ?B ?C  => apply (EqPointsNotCollinear X B C Y H); try immediate4
	| ~Collinear Y ?B ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X H); try immediate4
	| ~Collinear ?B X  ?C  => apply (EqPointsNotCollinear X B C Y); try immediate4
	| ~Collinear ?B Y  ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate4
	| ~Collinear ?B ?C X  => apply (EqPointsNotCollinear X B C Y); try immediate4
	| ~Collinear ?B ?C Y  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate4

	| Clockwise X ?B ?C  => apply (EqPointsNotCollinear X B C Y); try immediate4
	| Clockwise Y ?B ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate4
	| Clockwise ?B X  ?C  => apply (EqPointsNotCollinear X B C Y); try immediate4
	| Clockwise ?B Y  ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate4
	| Clockwise ?B ?C X  => apply (EqPointsNotCollinear X B C Y); try immediate4
	| Clockwise ?B ?C Y  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate4

	| DistancePlus (Distance ?A ?B) (Distance X Y) = _ => apply (DistancePlusRightCancell A B X Y); rewrite H; try immediate5
	| DistancePlus (Distance ?A ?B) (Distance Y X) = _ => apply sym_eq; apply (DistancePlusRightCancell A B Y X); rewrite H; try immediate5
	| _ = DistancePlus (Distance ?A ?B) (Distance X Y) => apply (DistancePlusRightCancell A B X Y); rewrite <- H; try immediate5
	| _ = DistancePlus (Distance ?A ?B) (Distance Y X) => apply sym_eq; apply (DistancePlusRightCancell A B Y X); rewrite <- H; try immediate5

	| DistancePlus (Distance X Y) (Distance ?A ?B) = _ => apply (DistancePlusLeftCancell A B X Y); rewrite H; try immediate5
	| DistancePlus (Distance Y X) (Distance ?A ?B) = _ => apply sym_eq; apply (DistancePlusLeftCancell A B Y X); rewrite H; try immediate5
	| _ = DistancePlus  (Distance X Y) (Distance ?A ?B) => apply (DistancePlusLeftCancell A B X Y); rewrite <- H; try immediate5
	| _ = DistancePlus (Distance Y X) (Distance ?A ?B) => apply sym_eq; apply (DistancePlusLeftCancell A B Y X); rewrite <- H; try immediate5

	| Angle ?C ?A ?B ?Hac ?Hab = Angle ?D ?A ?B ?Had ?Hab => eqToCongruent8; apply (EqAngleUniquePointSide1 A B C D); try immediate8
	| Angle ?B ?A ?C ?Hab ?Hac = Angle ?B ?A ?D ?Hab ?Had =>  eqToCongruent8; apply (EqAngleUniquePointSide2 A B C D); try immediate8

	| CongruentAngle ?C ?A ?B ?D ?A ?B =>  apply (EqAngleUniquePointSide1 A B C D H); try immediate8
	| CongruentAngle ?B ?A ?C ?B ?A ?D  => apply (EqAngleUniquePointSide2 A B C D H); try immediate8

	| IsAngle X => apply EqAngle; try immediate8
	| IsAngle Y => apply EqAngle; try immediate8

	| X = ?Z => rewrite H; try solveEq5
	| Y = ?Z => rewrite H; try solveEq5
	| ?Z = X => rewrite <- H; try solveEq5
	| ?Z = Y => rewrite <- H; try solveEq5

	| ?Z = ?T => first 
			[let Hyp := fresh in (assert (Hyp : X=Z); [solveEq5 | rewrite Hyp; clear Hyp; rewrite H; try solveEq5]) |
			let Hyp := fresh in (assert (Hyp : Y=Z); [solveEq5 | rewrite Hyp ; clear Hyp; rewrite H; try solveEq5]) |
			let Hyp := fresh in (assert (Hyp : X=T); [solveEq5 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq5]) |
			let Hyp := fresh in (assert (Hyp : Y=T); [solveEq5 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq5])]
end.

Ltac step12 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance10 H
	| |- _ = DistancePlus _ _  => stepEqDistance10 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance10 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance10 H
	| |- Distance _ _ = _ => stepEqDistance10 H
	| |- _ = Distance _ _ => stepEqDistance10 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |-  Supplement ?A ?B ?C ?D ?E ?F => stepSupplement11 A B C D E F H
	| |-  OpposedAngles ?A ?B ?C ?D ?E => stepOpposed8 A B C D E H

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent10; try immediate10
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent10; try immediate10

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle11 A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle8 A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle8 A B C H
	| |- RightAngle ?A ?B ?C => stepRightAngle12 A B C H

	| |- _ = H => try unfold H; byDefEqPoint11
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint11

	| |- ?A = ?B => stepEq12 A B H
	| |- ?A <> ?B => stepDistinct12 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct12 A B H

	| |- Collinear _ _ _  => stepCollinear6 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented11 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay6 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay6 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise9 A B C H
	| |- Between ?A ?B ?D => stepBetween8 A B D H
	| |- Segment ?A ?B ?C  => stepSegment8 A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec2 A B C D E F H

	| |- OnLine ?d ?M=> stepOnLine12 d M H
	| |- Diameter H ?c => unfold Diameter, H; simpl Center; stepOnLine9

	| |- TStrict ?t => stepTStrict7 t H

	| |- TCongruent _ _ => stepTCongruent7 H

	| |- Parallelogramm ?A ?B ?C ?D => stepParallelogramm11 A B C D H
	| |- StrictParallelogramm ?A ?B ?C ?D => stepStrictParallelogramm11 A B C D H

	| |- EqLine ?d1 ?d2 => stepEqLine12 d1 d2 H
	| |- ParallelLines ?d1 ?d2 => stepParallelLines12 d1 d2 H
	| |- SecantLines ?d1 ?d2 => stepSecantLines12 d1 d2 H
	| |- Perpendicular ?d1 ?d2 => stepPerpendicular12 d1 d2 H

end.

Ltac since12 txt := assert txt; try immediate12.

Ltac from12 H txt := assert txt; [(step12 H ; try immediate12) |  try immediate12].

Ltac as12 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate12 |( step12 Hyp ; try immediate12)]).

Ltac setPerpendicularPoint12 d1 d2 M := match goal with
| H : Perpendicular d1 d2 |- _ =>
	pose (M := PerpendicularPoint d1 d2 H);
	let Hyp1 := fresh in (
		assert (PerpendicularPointOnLine1 d1 d2 H);
		let Hyp2 := fresh in (
			assert (PerpendicularPointOnLine2 d1 d2 H);
			fold M in Hyp1, Hyp2))
| H : Perpendicular d2 d1 |- _ =>
	pose (M := PerpendicularPoint d1 d2 (PerpendicularSym d2 d1 H));
	let Hyp1 := fresh in (
		assert (PerpendicularPointOnLine1 d1 d2 (PerpendicularSym d2 d1 H));
		let Hyp2 := fresh in (
			assert (PerpendicularPointOnLine2 d1 d2 (PerpendicularSym d2 d1 H));
			fold M in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : Perpendicular d1 d2);
	[try immediate12 |
	pose (M := PerpendicularPoint d1 d2 H);
	let Hyp1 := fresh in (
		assert (PerpendicularPointOnLine1 d1 d2 H);
		let Hyp2 := fresh in (
			assert (PerpendicularPointOnLine2 d1 d2 H);
			fold M in Hyp1, Hyp2))])
end.
	