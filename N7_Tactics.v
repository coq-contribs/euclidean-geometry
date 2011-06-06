
Ltac solveEq13 := match goal with
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

	| |- ?A = LineA (Parallel ?d ?A ?H) => apply (LineAParallel d A H)
	| |- LineA (Parallel ?d ?A ?H) = ?A => apply sym_eq; apply (LineAParallel d A H)

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

Ltac immPerpendicular13 := match goal with 
	| H : Perpendicular ?d1 ?d2 |- Perpendicular ?d2 ?d1 => apply (PerpendicularSym d1 d2 H)

	| |- Perpendicular (Ruler ?A ?B ?Hab) (MidLine ?A ?B ?Hab) => apply (PerpendicularMidLine A B Hab)
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?A ?B ?Hab) => apply PerpendicularSym; apply (PerpendicularMidLine A B Hab)

	| |- Perpendicular (Ruler ?A ?B ?Hab') (MidLine ?A ?B ?Hab) => apply (EqEqPerpendicular (Ruler A B Hab) (Ruler A B Hab') (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineId A B Hab Hab') |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?A ?B ?Hab') => apply PerpendicularSym; apply (EqEqPerpendicular (Ruler A B Hab) (Ruler A B Hab') (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineId A B Hab Hab') |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]

	| |- Perpendicular (Ruler ?B ?A ?Hba) (MidLine ?A ?B ?Hab) => apply (EqEqPerpendicular (Ruler A B Hab) (Ruler B A Hba) (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineOpp A B Hab Hba) |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?B ?A ?Hba) => apply PerpendicularSym; apply (EqEqPerpendicular (Ruler A B Hab) (Ruler B A Hba) (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineOpp A B Hab Hba) |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]

	| |- Perpendicular ?l (PerpendicularDown ?l ?A ?H) => apply (PerpendicularDownPerpendicular l A H)
	| |- Perpendicular (PerpendicularDown ?l ?A ?H) ?l  => apply PerpendicularSym; apply (PerpendicularDownPerpendicular l A H)

	| |- Perpendicular ?l (PerpendicularUp ?l ?A ?H) => apply (PerpendicularUpPerpendicular l A H)
	| |- Perpendicular (PerpendicularUp ?l ?A ?H) ?l  => apply PerpendicularSym; apply (PerpendicularUpPerpendicular l A H)
end.

Ltac immParallelLines13 := match goal with 
	| |- ParallelLines ?d ?d  => apply ParallelLinesRefl
	| H : ParallelLines ?d1 ?d2 |- ParallelLines ?d2 ?d1 => apply (ParallelLinesSym d1 d2 H)
	| H : EqLine ?d1 ?d2 |- ParallelLines ?d1 ?d2 => apply (EqParallelLine d1 d2 H)
	| H : EqLine ?d1 ?d2 |- ParallelLines ?d2 ?d1 => apply ParallelLinesSym; apply (EqParallelLine d1 d2 H)

	| |- ParallelLines ?l (Parallel ?l ?A ?H) => apply (ParallelParallelLine l A H)
	| |- ParallelLines (Parallel ?l ?A ?H) ?l  => apply ParallelLinesSym; apply (ParallelParallelLine l A H)

	| _ => unfold ParallelLines; immediate11
end.

Ltac immNotSecantLines13 := match goal with 
	| H : EqLine ?d1 ?d2 |- ~SecantLines ?d1 ?d2 => apply (EqNotSecantLines d1 d2 H)
	| H : EqLine ?d2 ?d1 |- ~SecantLines ?d1 ?d2 => apply (EqNotSecantLines d1 d2 (EqLineSym d2 d1 H))

	| H : ~SecantLines ?d2 ?d1 |- ~SecantLines ?d1 ?d2 => contrapose0 H; apply (SecantLinesSym d1 d2 H)

	| |- ~SecantLines ?d (Parallel ?d _ _) => apply ParallelNotSecant
	| |- ~SecantLines (Parallel ?d ?A ?H) ?d => let Hyp := fresh in (intro Hyp; elim Hyp; apply ParallelLinesSym; apply (ParallelParallelLine d A H))

	| _ => let Hyp := fresh in (intro Hyp; elim Hyp; immParallelLines12)
end.

Ltac immOnLine13 := match goal with
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

	| |- OnLine  (PerpendicularDown ?d ?A ?H) ?A => apply (PerpendicularDownOnLine d A H)
	| |- OnLine  (PerpendicularUp ?d ?A ?H) ?A => apply (PerpendicularUpOnLine d A H)

	| |- OnLine  (Parallel ?d ?A ?H) ?A => apply (OnLineAParallel d A H)

	| |- OnLine (Ruler _ _ _) _ => simpl; immediate8
	| |- OnLine ?d _ => unfold d; simpl; immediate8
end.

Ltac immediate13 := match goal with 
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

	| |- _ = _ => solveEq13
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
	| |- OnLine _ _ => immOnLine13

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
	| |- ParallelLines _ _ => immParallelLines13
	| |- SecantLines _ _ => immSecantLines12
	| |- ~SecantLines _ _ => immNotSecantLines13
	| |- SecantLines ?d1 ?d2  -> False =>  fold (~SecantLines d1 d2); immNotSecantLines12
	| |- Perpendicular _ _ => immPerpendicular13
end.

Ltac stepEqLine13 d1 d2 H := match type of H with 
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

	| (Point*Line)%type => match H with
		| (?A, ?d0) => match goal with
			| Hp : ParallelLines d0 d1 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate13
			| Hp : ParallelLines d1 d0 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate13
			| Hp : ParallelLines d0 d2 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate13
			| Hp : ParallelLines d2 d0 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate13

			| Hp : Perpendicular d0 d1 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate13
			| Hp : Perpendicular d1 d0 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate13
			| Hp : Perpendicular d0 d2 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate13
			| Hp : Perpendicular d2 d0 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate13

		end
	end
end.

Ltac stepParallelLines13 d1 d2 H := match type of H with 
	| Line => apply (ParallelTrans d1 H d2); try immediate13

	| EqLine d1 ?d3  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1); [try immediate12 | apply (EqLineSym d1 d3 H)]
	| EqLine ?d3 d1  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1); [try immediate12 | apply H]
	| EqLine d2 ?d3  => apply (ParallelEqParallelLine d1 d3 d2); [try immediate12 | apply (EqLineSym d2 d3 H)]
	| EqLine ?d3 d2  => apply (ParallelEqParallelLine d1 d3 d2); [try immediate12 | apply H]
	
	| ParallelLines d1 ?d3  => apply (ParallelEqParallelLine d1 d3 d2 H); try immediate12
	| ParallelLines ?d3 d1  => apply (ParallelEqParallelLine d1 d3 d2 (ParallelLinesSym d3 d1 H)); try immediate12
	| ParallelLines d2 ?d3  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1 H); try immediate12
	| ParallelLines ?d3 d2  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1 (ParallelLinesSym d3 d2 H)); try immediate12
	
	| ParallelLines ?d3 ?d4  => apply (EqEqParallelLine d3 d4 d1 d2); try immediate12
	
	| Perpendicular d1 ?d3  => apply (PerpendicularPerpendicularParallel d1 d3 d2 H); try immediate13
	| Perpendicular ?d3 d1  => apply (PerpendicularPerpendicularParallel d1 d3 d2 (PerpendicularSym d3 d1 H)); try immediate13
	| Perpendicular d2 ?d3  => apply ParallelLinesSym; apply (PerpendicularPerpendicularParallel d2 d3 d1 H); try immediate13
	| Perpendicular ?d3 d2  => apply ParallelLinesSym; apply (PerpendicularPerpendicularParallel d2 d3 d1 (PerpendicularSym d3 d2 H)); try immediate13
end.

Ltac stepSecantLines13 d1 d2 H := match type of H with 
	| (Point*Point)%type => match H with 
		|  (?A, ?B) => apply (TwoPointsSecantLine d1 d2 A B); try immediate12
		end

	| ((Point*Point)*(Point*Point))%type => match H with
		|  ((?A, ?B), (?C, ?D)) => apply (FourPointsSecantLines d1 d2 A B C D); try immediate12
		end

	| (Line*Line)%type => match H with
		| (?d3,?d4) => match goal with
			| Hp : ParallelLines d1 d3 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d1 d4 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d3 d1 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d4 d1 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d2 d3 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d2 d4 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d3 d2 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13
			| Hp : ParallelLines d4 d2 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate13

			| Hp : Perpendicular d1 d3 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d1 d4 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d3 d1 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d4 d1 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d2 d3 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d2 d4 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d3 d2 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			| Hp : Perpendicular d4 d2 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate13
			end
		end

	| EqLine ?d3 d1  => apply (EqSecantSecantLines d3 d1 d2 H); try immediate12
	| EqLine d1 ?d3  => apply (EqSecantSecantLines d3 d1 d2 (EqLineSym d1 d3 H)); try immediate12
	| EqLine ?d3 d2  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1 H); try immediate12
	| EqLine d2 ?d3  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1  (EqLineSym d2 d3 H)); try immediate12

	| SecantLines ?d3 d2  => apply (EqSecantSecantLines d3 d1 d2); [try immediate12 | apply H]
	| SecantLines d2 ?d3  =>  apply (EqSecantSecantLines d3 d1 d2); [try immediate12 | apply (SecantLinesSym d2 d3 H)]
	| SecantLines ?d3 d1  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1); [try immediate12 | apply H]
	| SecantLines d1 ?d3  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1); [try immediate12 | apply (SecantLinesSym d1 d3 H)]

	| SecantLines ?d3 ?d4  => apply (EqEqSecantSecantLines d3 d1 d4 d2); try immediate12

	| ParallelLines ?d0 d1  => apply (ParallelSecant d0 d1 d2 H); try immediate13
	| ParallelLines d1 ?d0  => apply (ParallelSecant d0 d1 d2); try immediate13
	| ParallelLines ?d0 d2  => apply ParallelLinesSym; apply (ParallelSecant d0 d2 d1 H); try immediate13
	| ParallelLines d2 ?d0  => apply ParallelLinesSym; apply (ParallelSecant d0 d2 d1); try immediate13
	
end.

Ltac stepPerpendicular13 d1 d2 H := match H with 
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
	
		| ParallelLines ?d0 d2  => apply (PerpendicularParallelPerpendicular d0 d1 d2); try immediate13
		| ParallelLines d2 ?d0  => apply (PerpendicularParallelPerpendicular d0 d1 d2); try immediate13
		| ParallelLines ?d0 d1  => apply ParallelLinesSym; apply (PerpendicularParallelPerpendicular d0 d2 d1); try immediate13
		| ParallelLines d1 ?d0  => apply ParallelLinesSym; apply (PerpendicularParallelPerpendicular d0 d2 d1); try immediate13
	end
end.

Ltac step13 H := match goal with
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

	| |- EqLine ?d1 ?d2 => stepEqLine13 d1 d2 H
	| |- ParallelLines ?d1 ?d2 => stepParallelLines13 d1 d2 H
	| |- SecantLines ?d1 ?d2 => stepSecantLines13 d1 d2 H
	| |- Perpendicular ?d1 ?d2 => stepPerpendicular13 d1 d2 H

end.

Ltac since13 txt := assert txt; try immediate13.

Ltac from13 H txt := assert txt; [(step13 H ; try immediate13) |  try immediate13].

Ltac as13 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate13 |( step13 Hyp ; try immediate13)]).

Ltac setPerpendicularDown13 l1 A l2 := match goal with
| H : ~OnLine l1 A |- _ => 
	pose (l2 := PerpendicularDown l1 A H);
	let Hyp1 := fresh in (
		assert (Hyp1 := PerpendicularDownOnLine l1 A H);
		let Hyp2 := fresh in (
			assert (Hyp2 := PerpendicularDownPerpendicular l1 A H);
				fold l2 in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : ~OnLine l1 A);
	[try immediate13  | pose (l2 := PerpendicularDown l1 A H);
		let Hyp1 := fresh in (
			assert (Hyp1 := PerpendicularDownOnLine l1 A H);
			let Hyp2 := fresh in (
				assert (Hyp2 := PerpendicularDownPerpendicular l1 A H);
					fold l2 in Hyp1, Hyp2))])
end.

Ltac setPerpendicularUp13 l1 A l2 := match goal with
| H : OnLine l1 A |- _ => 
	pose (l2 := PerpendicularUp l1 A H);
	let Hyp1 := fresh in (
		assert (Hyp1 := PerpendicularUpOnLine l1 A H);
		let Hyp2 := fresh in (
			assert (Hyp2 := PerpendicularUpPerpendicular l1 A H);
				fold l2 in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : OnLine l1 A);
	[try immediate13 | pose (l2 := PerpendicularUp l1 A H);
		let Hyp1 := fresh in (
			assert (Hyp1 := PerpendicularUpOnLine l1 A H);
			let Hyp2 := fresh in (
				assert (Hyp2 := PerpendicularUpPerpendicular l1 A H);
					fold l2 in Hyp1, Hyp2))])
end.

Ltac setParallel13 l1 A l2 := match goal with
	| H : ~OnLine l1 A |- _ => 
		pose (l2 := Parallel l1 A H);
		let Hyp1 := fresh in (
			assert (Hyp1 := OnLineAParallel l1 A H);
			let Hyp2 := fresh in (
				assert (Hyp2 :=  ParallelParallelLine l1 A H);
				fold l2 in Hyp1, Hyp2))
	| _ => let H := fresh in (
			assert (H : ~OnLine l1 A);
			[immediate13 | pose (l2 := Parallel l1 A H);
				let Hyp1 := fresh in (
					assert (Hyp1 := OnLineAParallel l1 A H);
					let Hyp2 := fresh in (
						assert (Hyp2 :=  ParallelParallelLine l1 A H);
						fold l2 in Hyp1, Hyp2))])
end.

Ltac byPaschCases13 A B C D l E := match goal with
| Hnc : ~Collinear A B C |- _ => match goal with
	| Hb : Between A D B |- _ => match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate13 |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end])
		end
	| _ =>let Hb := fresh in (assert (Hb : Between A D B);
		[try immediate13 |  match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate13 |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end])
		end])
	end
|  _ => let Hnc := fresh in (assert (Hnc : ~Collinear A B C);
	[try immediate13 | match goal with
	| Hb : Between A D B |- _ => match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate13 |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end])
		end
	| _ =>let Hb := fresh in (assert (Hb : Between A D B);
		[try immediate13 |  match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate13 |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate13 | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate13 |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate13 | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate13 |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hnc Hb Hd Hna Hnb Hnc) as (E, (Hypb, Hypo))])
						end])
				end])
			end])
		end])
	end])
end.

