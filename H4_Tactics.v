Require Import A1_Plan A2_Orientation A4_Droite A5_Cercle .
Require Import B1_ClockwiseProp B2_CollinearProp B4_RaysProp B5_BetweenProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D2_ExistsClockwise D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics .
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F5_Tactics .
Require Import G1_Angles G3_ParticularAngle G4_Tactics .
Require Import H1_Triangles H2_ParticularTriangles H3_BuildingTriangle.


Ltac setTriangle7 A B C t := pose (t:=Tr A B C).

Ltac usingSSS7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply SSSTCongruent
	| |- TCongruent ?t1 _ => unfold t1; usingSSS7
	| |- TCongruent _ ?t2 => unfold t2; usingSSS7
end.

Ltac usingSASb7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply (SASTCongruent A1 B1 C1 A2 B2 C2)
	| |- TCongruent ?t1 _ => unfold t1; usingSASb7
	| |- TCongruent _ ?t2 => unfold t2; usingSASb7
end.

Ltac usingSASa7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply TCongruentPerm; apply (SASTCongruent  C1 A1 B1 C2 A2 B2)
	| |- TCongruent ?t1 _ => unfold t1; usingSASa7
	| |- TCongruent _ ?t2 => unfold t2; usingSASa7
end.

Ltac usingSASc7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => do 2 apply TCongruentPerm; apply (SASTCongruent B1 C1 A1 B2 C2 A2)
	| |- TCongruent ?t1 _ => unfold t1; usingSASc7
	| |- TCongruent _ ?t2 => unfold t2; usingSASc7
end.

Ltac usingASAca7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply (ASATCongruent A1 B1 C1 A2 B2 C2)
	| |- TCongruent ?t1 _ => unfold t1; usingASAca7
	| |- TCongruent _ ?t2 => unfold t2; usingASAca7
end.

Ltac usingASAbc7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) =>  apply TCongruentPerm; apply (ASATCongruent  C1 A1 B1 C2 A2 B2)
	| |- TCongruent ?t1 _ => unfold t1; usingASAbc7
	| |- TCongruent _ ?t2 => unfold t2; usingASAbc7
end.

Ltac usingASAab7 := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) =>  do 2 apply TCongruentPerm;apply (ASATCongruent B1 C1 A1 B2 C2 A2)
	| |- TCongruent ?t1 _ => unfold t1; usingASAab7
	| |- TCongruent _ ?t2 => unfold t2; usingASAab7
end.

Ltac immIsoscelesOne7 := match goal with
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?A ?B ?C) => exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?C ?A ?B) => apply Isosceles31; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?C ?B ?A) => apply Isosceles1Sym; apply Isosceles31; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?B ?C ?A) => apply Isosceles31;  apply Isosceles23; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?B ?A ?C) => apply Isosceles1Sym; apply Isosceles31;  apply Isosceles23; exact H

	| H : Distance ?A ?B = Distance ?A ?C |-  Isosceles1 (Tr ?A ?B ?C) => simpl; exact H
	| H : Distance ?B ?A = Distance ?A ?C |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?A ?B = Distance ?C ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?B ?A = Distance ?C ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?A ?C = Distance ?A ?B |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?C ?A = Distance ?A ?B |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?A ?C = Distance ?B ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?C ?A = Distance ?B ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; immediate6 

	| H : CongruentAngle ?A ?B ?C  ?A ?C ?B   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C ); immediate6  
	| H : CongruentAngle ?C ?B ?A  ?A ?C ?B   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C); immediate6 
	| H : CongruentAngle ?A ?B ?C  ?B ?C ?A   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C); immediate6 
	| H : CongruentAngle ?C ?B ?A  ?B ?C ?A   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C); immediate6 
	| H : CongruentAngle ?A ?B ?C   ?A ?C ?B  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); immediate6 
	| H : CongruentAngle ?C ?B ?A ?A ?C ?B  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); immediate6 
	| H : CongruentAngle ?A ?B ?C  ?B ?C ?A  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); immediate6 
	| H : CongruentAngle ?C ?B ?A   ?B ?C ?A  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); immediate6 
end.

Ltac immIsoscelesTwo7 := match goal with
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?A ?B ?C) => exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?C ?A ?B) => apply Isosceles12; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?C ?B ?A) => apply Isosceles2Sym; apply Isosceles12; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?B ?C ?A) => apply Isosceles12;  apply Isosceles31; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?B ?A ?C) => apply Isosceles2Sym; apply Isosceles12;  apply Isosceles31; exact H

	| H : Distance ?B ?C = Distance ?B ?A |-  Isosceles2 (Tr ?A ?B ?C) => simpl; exact H
	| H : Distance ?C ?B = Distance ?B ?A |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?B ?C = Distance ?A ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?C ?B = Distance ?A ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?B ?A = Distance ?B ?C |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?A ?B = Distance ?B ?C |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?B ?A = Distance ?C ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?A ?B = Distance ?C ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; immediate6 

	| H : CongruentAngle ?B ?C ?A ?B ?A ?C  |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C  ); immediate6  
	| H : CongruentAngle ?A ?C ?B ?B ?A ?C   |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C ); immediate6 
	| H : CongruentAngle ?B ?C ?A ?C ?A ?B  |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C ); immediate6 
	| H : CongruentAngle ?A ?C ?B  ?C ?A ?B  |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C ); immediate6 
	| H : CongruentAngle ?B ?C ?A ?B ?A ?C |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); immediate6 
	| H : CongruentAngle ?A ?C ?B  ?B ?A ?C  |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); immediate6 
	| H : CongruentAngle ?B ?C ?A  ?C ?A ?B  |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); immediate6 
	| H : CongruentAngle ?A ?C ?B  ?C ?A ?B   |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); immediate6 
end.

Ltac immIsoscelesThree7 := match goal with
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?A ?B ?C) => exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?C ?A ?B) => apply Isosceles23; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?C ?B ?A) => apply Isosceles3Sym; apply Isosceles23; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?B ?C ?A) => apply Isosceles23;  apply Isosceles12; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?B ?A ?C) => apply Isosceles3Sym; apply Isosceles23;  apply Isosceles12; exact H

	| H : Distance ?C ?A = Distance ?C ?B |-  Isosceles3 (Tr ?A ?B ?C) => simpl; exact H
	| H : Distance ?A ?C = Distance ?C ?B |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?C ?A = Distance ?B ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?A ?C = Distance ?B ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?C ?B = Distance ?C ?A |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?B ?C = Distance ?C ?A |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6
	| H : Distance ?C ?B = Distance ?A ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6 
	| H : Distance ?B ?C = Distance ?A ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; immediate6 

	| H : CongruentAngle ?C ?A ?B ?C ?B ?A  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C ); immediate6  
	| H : CongruentAngle ?B ?A ?C  ?C ?B ?A  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C); immediate6 
	| H : CongruentAngle ?C ?A ?B ?A ?B ?C  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C ); immediate6 
	| H : CongruentAngle ?B ?A ?C  ?A ?B ?C  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C ); immediate6 
	| H : CongruentAngle ?C ?A ?B  ?C ?B ?A  |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); immediate6 
	| H : CongruentAngle ?B ?A ?C  ?C ?B ?A  |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); immediate6 
	| H : CongruentAngle ?C ?A ?B  ?A ?B ?C  |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); immediate6 
	| H : CongruentAngle ?B ?A ?C ?A ?B ?C   |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); immediate6 
end.

Ltac immEquilateral7 := 
match goal with
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?A ?B ?C) => exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?A ?C ?B) => apply EquilateralSym; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?C ?A ?B) => do 2 apply EquilateralPerm; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?C ?B ?A) => apply EquilateralSym; do 2 apply EquilateralPerm; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?B ?C ?A) => apply EquilateralPerm; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?B ?A ?C) => apply EquilateralSym; apply EquilateralPerm; exact H

	| |- Equilateral (Tr ?A ?B ?C) => solve 
		[ apply Isosceles12Equilateral; [immIsoscelesOne7 | immIsoscelesTwo7] |
		 apply Isosceles23Equilateral; [immIsoscelesTwo7 | immIsoscelesThree7] |
		 apply Isosceles31Equilateral; [immIsoscelesThree7 | immIsoscelesOne7] ]
end.

Ltac generalizeDistIsosceles7 := repeat match goal with
	| H : Isosceles1 _ |- _ => generalize H; simpl in H; generalize H; clear H
	| H : Isosceles2 _ |- _ => generalize H; simpl in H; generalize H; clear H
	| H : Isosceles3 _ |- _ => generalize H; simpl in H; generalize H; clear H

	| H : Equilateral (Tr ?A ?B ?C) |- _ => 
		generalize (EquilateralEqSides12 A B C H); 
		generalize (EquilateralEqSides23 A B C H); 
		generalize (EquilateralEqSides31 A B C H);
		generalize H; clear H
end.

Ltac generalizeDistTCongruent7 := repeat match goal with
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- _ => 
		generalize (TCongruentEqSidesAB A B C D E F H);
		generalize (TCongruentEqSidesBC A B C D E F H);
		generalize (TCongruentEqSidesCA A B C D E F H);
		generalize H; clear H
end.
 
Ltac solveDist7 :=try solveOnCircleDist2; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2;  unfoldDistance2; solveEq2.

Ltac solveDistPlus7 := generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistancePlus2; unfoldDistancePlus2; substDistancePlus2; solveEq2.

Ltac solveDistTimes7 := generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistanceTimes2; unfoldDistanceTimes2; substDistanceTimes2; solveEq2.

Ltac solveDistance7 := simplDistance6; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus7
	| |- _ = DistancePlus _ _ => solveDistPlus7

	| |- DistanceTimes _ _ _ = _ => solveDistTimes7
	| |- _ = DistanceTimes _ _ _ => solveDistTimes7

	| |- Distance _ _ = _ => solveDist7
	| |- _ = Distance _ _ => apply sym_eq; solveDist7

	| |- _ => solveEq5
end.

Ltac solveEq7 := match goal with
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

	| H1 : IsAngle ?alpha, H2 : IsAngle ?beta |- ?alpha = ?beta => apply (EqAngle alpha beta H1 H2); solveDistance6

	| |- ?A = ?B => match type of A with
			| Point => let H := fresh in (assert (H : Distance A B = Oo); [solveDistance7 | apply (NullDistanceEq A B H)])
			end

	| |- ?X = _ => unfold X; solveEq7
	| |- _ = ?Y => unfold Y; solveEq7
end.

Ltac immTStrict7 := match goal with 
	| H: TStrict ?t |- TStrict ?t => exact H
	| |- TStrict (Tr ?A ?B ?C) => (right; immClockwise1) || (left; immClockwise1)
	| |- TStrict ?t => unfold t;  (right; immClockwise1) || (left; immClockwise1)
end.

Ltac immDistinct7 := match goal with
	| H : ?A <> ?B |- ?A <> ?B => exact H
	| H : ?A <> ?B |- ?B <> ?A => auto
	| H : ?A = ?B -> False |- ?A <> ?B => exact H
	| H : ?A = ?B -> False |- ?B <> ?A => auto

	| |- Oo <> Uu => exact DistinctOoUu
	| |- Uu <> Oo => apply sym_not_eq; exact DistinctOoUu

	| |- Oo <> uU => exact DistinctOouU
	| |- uU <> Oo => apply sym_not_eq; exact DistinctOouU

	| |- Uu <> uU => exact DistinctUuuU
	| |- uU <> Uu => apply sym_not_eq; exact DistinctUuuU

	| H : IsAngle ?A  |- Oo <> ?A => exact (IsAngleDistinctOo A H)
	| H : IsAngle ?A  |- ?A <> Oo => apply sym_not_eq;  exact (IsAngleDistinctOo A H)

	| |- LineA ?l <> LineB ?l => apply (LineH l)
	| |- LineB ?l <> LineA ?l => apply (sym_not_eq (LineH l))

	| |- ?A <> SymmetricPoint ?A _ _ => apply DistinctASymmetricPoint
	| |- SymmetricPoint ?A _ _ <> ?A => apply sym_not_eq; apply DistinctASymmetricPoint
	| |- ?B <> SymmetricPoint _ ?B _ => apply DistinctBSymmetricPoint
	| |- SymmetricPoint _ ?B _ <> ?B => apply sym_not_eq; apply DistinctBSymmetricPoint

	| |- Graduation ?n ?A ?B ?Hab <> Graduation (S ?n) ?A ?B ?Hab => apply GraduationDistinctnSn
	| |- Graduation (S ?n) ?A ?B ?Hab <> Graduation ?n ?A ?B ?Hab => apply sym_not_eq; apply GraduationDistinctnSn

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

	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?B <> ?A => apply (CongruentAngleDistinctBA _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?A <> ?B => apply sym_not_eq; apply (CongruentAngleDistinctBA _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?B <> ?C => apply (CongruentAngleDistinctBC _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?C <> ?B => apply sym_not_eq; apply (CongruentAngleDistinctBC _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?E <> ?D => apply (CongruentAngleDistinctED _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?D <> ?E => apply sym_not_eq; apply (CongruentAngleDistinctED _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?E <> ?F => apply (CongruentAngleDistinctEF _ _ _ _ _ _ H)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- ?F <> ?E => apply sym_not_eq; apply (CongruentAngleDistinctEF _ _ _ _ _ _ H)

	| H : NullAngle ?A ?B ?C |- ?B <> ?A => apply (NullAngleDistinctBA _ _ _ H)
	| H : NullAngle ?A ?B ?C |- ?A <> ?B => apply sym_not_eq; apply (NullAngleDistinctBA _ _ _ H)
	| H : NullAngle ?A ?B ?C |- ?B <> ?C => apply (NullAngleDistinctBC _ _ _ H)
	| H : NullAngle ?A ?B ?C |- ?C <> ?B => apply sym_not_eq; apply (NullAngleDistinctBC _ _ _ H)

	| H : ElongatedAngle ?A ?B ?C |- ?B <> ?A => apply (ElongatedAngleDistinctBA _ _ _ H)
	| H : ElongatedAngle ?A ?B ?C |- ?A <> ?B => apply sym_not_eq; apply (ElongatedAngleDistinctBA _ _ _ H)
	| H : ElongatedAngle ?A ?B ?C |- ?B <> ?C => apply (ElongatedAngleDistinctBC _ _ _ H)
	| H : ElongatedAngle ?A ?B ?C |- ?C <> ?B => apply sym_not_eq; apply (ElongatedAngleDistinctBC _ _ _ H)

	| H : TStrict (Tr ?A ?B _) |- ?A <> ?B => apply (TStrictDistinctAB _ _ _ H)
	| H : TStrict (Tr ?A ?B _) |- ?B <> ?A => apply sym_not_eq; apply (TStrictDistinctAB _ _ _ H)
	| H : TStrict (Tr ?A _ ?C) |- ?C <> ?A => apply (TStrictDistinctCA _ _ _ H)
	| H : TStrict (Tr ?A _ ?C) |- ?A <> ?C => apply sym_not_eq; apply (TStrictDistinctCA _ _ _ H)
	| H : TStrict (Tr _ ?B ?C) |- ?B <> ?C => apply (TStrictDistinctBC _ _ _ H)
	| H : TStrict (Tr _ ?B ?C) |- ?C <> ?B => apply sym_not_eq; apply (TStrictDistinctBC _ _ _ H)
end.

Ltac orderAngle7 A B C D E F  := match goal with 
	| |- CongruentAngle A B C D E F => idtac
	| |- CongruentAngle C B A D E F =>  apply CongruentAngleRev1 
	| |- CongruentAngle A B C F E D => apply CongruentAngleRev2
	| |- CongruentAngle C B A F E D =>  apply CongruentAngleRev
 
	| |- CongruentAngle D E F A B C=>  apply CongruentAngleSym
	| |- CongruentAngle D E F C B A=>   apply CongruentAngleSym; apply CongruentAngleRev1 
	| |- CongruentAngle F E D A B C=>  apply CongruentAngleSym; apply CongruentAngleRev2
	| |- CongruentAngle F E D C B A=>   apply CongruentAngleSym; apply CongruentAngleRev
 end.

Ltac immCongruentAngle7 := match goal with 
	| |- CongruentAngle ?A ?B ?C ?A ?B ?C => apply (CongruentAngleRefl A B C); try immDistinct6
	| |- CongruentAngle ?A ?B ?C ?C ?B ?A => apply (CongruentAnglePerm A B C);  try immDistinct6

	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- _ => orderAngle7 A B C D E F; exact H 

	|H : Angle ?A ?B ?C ?H1 ?H2  = Angle ?D ?E ?F ?H3 ?H4  |- _ => orderAngle7 A B C D E F; apply (CongruentEqAngle A B C D E F H1 H2 H3 H4 H)

	| H : OpenRay ?B ?A ?D |- CongruentAngle ?A ?B ?C ?D ?B ?C => apply (CongruentAngleSide1 A B C D); immediate5
	| H : OpenRay ?B ?C ?D |- CongruentAngle ?A ?B ?C ?A ?B ?D => apply (CongruentAngleSide2 A B C D); immediate5
	| H1 : OpenRay ?B ?A ?D, H2 : OpenRay ?B ?C ?E |- CongruentAngle ?A ?B ?C ?D ?B ?E => apply (CongruentAngleSides A B C D E); immediate5

	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?A1 _ _ ?A2 _ => orderAngle7  C1 A1 B1 C2 A2 B2; apply TCongruentAnglesA; immediate6
	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?A2 _ _ ?A1 _ => orderAngle7  C1 A1 B1 C2 A2 B2; apply TCongruentAnglesA; immediate6

	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?B1 _ _ ?B2 _ => orderAngle7  A1 B1 C1 A2 B2 C2; apply TCongruentAnglesB; immediate6
	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?B2 _ _ ?B1 _ => orderAngle7  A1 B1 C1 A2 B2 C2; apply TCongruentAnglesB; immediate6

	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?C1 _ _ ?C2 _ => orderAngle7  B1 C1 A1 B2 C2 A2; apply TCongruentAnglesC; immediate6
	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?C2 _ _ ?C1 _ => orderAngle7  B1 C1 A1 B2 C2 A2; apply TCongruentAnglesC; immediate6

	| H : Isosceles1 (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?C _ => orderAngle7  A B C A C B; apply IsoscelesEqAngles1; immediate6
	| H : Isosceles1 (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?B _ => orderAngle7  A B C A C B; apply IsoscelesEqAngles1; immediate6

	| H : Isosceles2 (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?A _ => orderAngle7  B C A B A C; apply IsoscelesEqAngles2; immediate6
	| H : Isosceles2 (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?C _ => orderAngle7  B C A B A C; apply IsoscelesEqAngles2; immediate6

	| H : Isosceles3 (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?B _ => orderAngle7  C A B C B A; apply IsoscelesEqAngles3; immediate6
	| H : Isosceles3 (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?A _ => orderAngle7   C A B C B A; apply IsoscelesEqAngles3; immediate6

	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?C _ => orderAngle7  A B C A C B; apply IsoscelesEqAngles1; [immediate6 | immediate6 | immediate6 | exact (EquilateralIsosceles1 A B C H)]
	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?B _ => orderAngle7  A B C A C B; apply IsoscelesEqAngles1; [immediate6 | immediate6 | immediate6 | exact (EquilateralIsosceles1 A B C H)]

	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?A _ => orderAngle7  B C A B A C; apply IsoscelesEqAngles2; [immediate6 | immediate6 | immediate6 | exact (EquilateralIsosceles2 A B C H)]
	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?C _ => orderAngle7  B C A B A C; apply IsoscelesEqAngles2; [immediate6 | immediate6 | immediate6 | exact (EquilateralIsosceles2 A B C H)]

	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?B _ => orderAngle7  C A B C B A; apply IsoscelesEqAngles3; [immediate6 | immediate6 | immediate6 | exact (EquilateralIsosceles3 A B C H)]
	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?A _ => orderAngle7   C A B C B A; apply IsoscelesEqAngles3; [immediate6 | immediate6 | immediate6 | exact (EquilateralIsosceles3 A B C H)]

end.

Ltac solveAngle7 := match goal with 
	| |- Angle _ _ _ _ _ = Angle _ _ _ _ _ => apply EqCongruentAngle; immCongruentAngle7

	| |- Angle ?A ?B ?C _ _ = Uu => eqToCongruent6; immNullAngle6
	| |- Uu = Angle ?A ?B ?C _ _ => eqToCongruent6; immNullAngle6

	| |- Angle ?A ?B ?C _ _ = uU => eqToCongruent6; immElongatedAngle6
	| |- uU = Angle ?A ?B ?C _ _ => eqToCongruent6; immElongatedAngle6

	| |- Angle Uu Oo ?M _ _ = ?M => apply EqAnglePoint; immIsAngle6
	| |- ?M = Angle Uu Oo ?M _ _  => apply sym_eq; apply EqAnglePoint; immIsAngle6
	| |- Angle ?M Oo Uu ?H1 ?H2 = ?M => rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2));  apply EqAnglePoint; immIsAngle6
	| |- ?M = Angle ?M Oo Uu ?H1 ?H2  => apply sym_eq;  rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2)); apply EqAnglePoint; immIsAngle6

end.

Ltac immTCongruent7 := match goal with
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) => exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?B ?C ?A) (Tr ?E ?F ?D) => apply TCongruentPerm; exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?C ?A ?B) (Tr ?F ?D ?E) => do 2 apply TCongruentPerm; exact H

	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?D ?E ?F) (Tr ?A ?B ?C) => apply TCongruentSym; exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?E ?F ?D) (Tr ?B ?C ?A) => apply TCongruentSym;  apply TCongruentPerm; exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?F ?D ?E) (Tr ?C ?A ?B) => apply TCongruentSym; do 2 apply TCongruentPerm; exact H

	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?B ?A ?C) (Tr ?E ?D ?F) => apply TCongruentSubst;  exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?C ?B ?A) (Tr ?F ?E ?D) => apply TCongruentSubst; apply TCongruentPerm; exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?A ?C ?B) (Tr ?D ?F ?E) => apply TCongruentSubst; do 2 apply TCongruentPerm; exact H

	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?E ?D ?F) (Tr ?B ?A ?C) => apply TCongruentSubst; apply TCongruentSym; exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?F ?E ?D) (Tr ?C ?B ?A) => apply TCongruentSubst; apply TCongruentSym;  apply TCongruentPerm; exact H
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- TCongruent (Tr ?D ?F ?E) (Tr ?A ?C ?B) => apply TCongruentSubst; apply TCongruentSym; do 2 apply TCongruentPerm; exact H

	| |- TCongruent ?t1 _ => unfold t1; immTCongruent7
	| |- TCongruent _ ?t2 => unfold t2; immTCongruent7
	
	| _ => solve [usingSSS7; immediate6
				| usingSASa7; immediate6
				| usingSASb7; immediate6 
				| usingSASc7; immediate6
				| usingASAab7; immediate6 
				| usingASAbc7; immediate6
				| usingASAca7; immediate6]

end.

Ltac immediate7 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate7
	| |- ?A \/ ?B => (left; immediate7)  || (right; immediate7)

	| |- DistancePlus _ _ = _ => solveDistance7
	| |- _ = DistancePlus _ _ => solveDistance7

	| |- DistanceTimes _ _ _ = _ => solveDistance7
	| |- _ = DistanceTimes _ _ _ => solveDistance7

	| |- Distance _ _ = _ => solveDistance7
	| |- _ = Distance _ _ => solveDistance7

	| |- IsDistance ?d => immIsDistance2 d

	| |- Angle _ _ _ _ _ = _ => solveAngle7
	| |-  _ = Angle _ _ _ _ _ => solveAngle7

	| |- CongruentAngle _ _ _ _ _ _ => immCongruentAngle7
	| |- NullAngle _ _ _ => immNullAngle6
	| |- ElongatedAngle _ _ _ => immElongatedAngle6
	| |- ~NullAngle _ _ _ => immNotNullAngle6
	| |- ~ElongatedAngle _ _ _ => immNotElongatedAngle6

	| |- IsAngle _ => immIsAngle6

	| |- _ = _ => solveEq7
	| |- _ <> _ => immDistinct7
	| |- ?A = ?B -> False => fold(A <> B); immDistinct7

	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise6
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise6

	| |- Collinear _ _ _ => immCollinear6
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1

	| |- EquiOriented _ _ _ _ => immEquiOriented5
	| |- OpenRay _ _ _ => immOpenRay6
	| |- ClosedRay _ _ _ => immClosedRay6
	| |- Between _ _ _ => immBetween6
	| |- Segment _ _ _ => immSegment6

	| |- EquiDirected _ _ _ _ => immEquiDirected1
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected4
	| |- EquiDirected ?A ?B ?C ?D  -> False =>fold (~EquiDirected A B C D); immNotEquiDirected4

	| |- DistanceLe _ _ => immDistanceLe2
	| |- DistanceLt _ _ => immDistanceLt3

	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality3
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec3

	| |- Diameter _ _ => immDiameter2
	| |- SecantLines _ _ => immSecantLines4

	| |- OnCircle _ _ => immOnCircle6
	| |- OnLine _ _ => immOnLine5

	| |- TStrict _ => immTStrict7
	| |- Isosceles1 ?t => unfold t; immIsoscelesOne7
	| |- Isosceles1 (Tr _ _ _) => immIsoscelesOne7
	| |- Isosceles2 ?t => unfold t; immIsoscelesTwo7
	| |- Isosceles2 (Tr _ _ _) => immIsoscelesTwo7
	| |- Isosceles3 ?t => unfold t; immIsoscelesThree7
	| |- Isosceles3 (Tr _ _ _) => immIsoscelesThree7
	| |- Equilateral ?t => unfold t; immEquilateral7
	| |- Equilateral (Tr _ _ _) => immEquilateral7

	| |- TCongruent _ _ => immTCongruent7
end.

Ltac stepEqDistance7 H  := 
 repeat rewrite <- DistancePlusAssoc;
 repeat rewrite <- DistancePlusAssoc in H;
match type of H with
	| DistancePlus _ _  = _ => foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| _ = DistancePlus _ _  => foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| DistanceTimes _ _ _  = _ => foldDistanceTimesIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| _ = DistanceTimes _ _ _  => foldDistanceTimesIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| Distance _ _ = _ => foldDistanceIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| _ = Distance _ _ => foldDistanceIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H

	| OnCircle (Compass _ _ _) _  => unfold OnCircle in H; foldDistanceIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| OnCircle ?c _  => unfold c, OnCircle in  H; foldDistanceIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H

	| Isosceles1 (Tr _ _ _) => generalize H; intro; simpl in H;  foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| Isosceles2 (Tr _ _ _) => generalize H; intro; simpl in H;  foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| Isosceles3 (Tr _ _ _) => generalize H; intro; simpl in H;  foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| Isosceles1 ?t => generalize H; intro; unfold t in H; simpl in H; foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| Isosceles2 ?t => generalize H; intro; unfold t in H; simpl in H; foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| Isosceles3 ?t => generalize H; intro; unfold t in H; simpl in H; foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H

	| Equilateral (Tr ?A ?B ?C) => 
		let Hyp := fresh in (assert  (Hyp := EquilateralEqSides12 A B C H); foldDistanceIn2 Hyp;  foldDistanceTimesIn2 Hyp; foldDistancePlusIn2 Hyp; substDistanceIn2 Hyp; unfoldDistanceIn2 Hyp; unfoldDistancePlusIn2 Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := EquilateralEqSides23 A B C H); foldDistanceIn2 Hyp;  foldDistanceTimesIn2 Hyp; foldDistancePlusIn2 Hyp; substDistanceIn2 Hyp; unfoldDistanceIn2 Hyp; unfoldDistancePlusIn2 Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := EquilateralEqSides31 A B C H);foldDistanceIn2 Hyp;  foldDistanceTimesIn2 Hyp; foldDistancePlusIn2 Hyp; substDistanceIn2 Hyp; unfoldDistanceIn2 Hyp; unfoldDistancePlusIn2 Hyp) 
	| Equilateral ?t => unfold t in H; stepEqDistance7 H

	| TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) => 	
		let Hyp := fresh in (assert  (Hyp := TCongruentEqSidesAB A B C D E F H);  foldDistanceIn2 Hyp;  foldDistanceTimesIn2 Hyp; foldDistancePlusIn2 Hyp; substDistanceIn2 Hyp; unfoldDistanceIn2 Hyp; unfoldDistancePlusIn2 Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := TCongruentEqSidesBC A B C D E F H);  foldDistanceIn2 Hyp;  foldDistanceTimesIn2 Hyp; foldDistancePlusIn2 Hyp; substDistanceIn2 Hyp; unfoldDistanceIn2 Hyp; unfoldDistancePlusIn2 Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := TCongruentEqSidesCA A B C D E F H);  foldDistanceIn2 Hyp;  foldDistanceTimesIn2 Hyp; foldDistancePlusIn2 Hyp; substDistanceIn2 Hyp; unfoldDistanceIn2 Hyp; unfoldDistancePlusIn2 Hyp) 
	| TCongruent ?t1 _ => unfold t1; stepEqDistance7 H
	| TCongruent _ ?t2 => unfold t2; stepEqDistance7 H

	| Point => apply trans_eq with (y := H)

end; try immediate7.

Ltac stepTStrict7 t H := match type of H with
	| TCongruent ?t1 t => apply (TCongruentTStrict t1 t H); try immTStrict7
	| TCongruent t ?t1 => apply (TCongruentTStrict t1 t (TCongruentSym t t1 H)); try immTStrict7

	| TStrict ?t1 => apply (TCongruentTStrict t1 t); try immediate7
	| Clockwise ?A ?B ?C => apply (TCongruentTStrict (Tr A B C) t); try immediate7
end.

Ltac stepTCongruentTrans7 H := match goal  with
	| |- TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) => match type of H with
		| TCongruent (Tr A B C) (Tr ?D' ?E' ?F') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F) H)
		| TCongruent (Tr B C A) (Tr  ?E' ?F' ?D') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr C A B) (Tr  ?F' ?D'  ?E') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr B A C) (Tr ?E' ?D' ?F') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr A C B) (Tr  ?D' ?F' ?E') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr C B A) (Tr  ?F' ?E'  ?D') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?D' ?E' ?F') (Tr A B C) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr  ?E' ?F' ?D') (Tr B C A) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr  ?F' ?D'  ?E') (Tr C A B) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?E' ?D' ?F') (Tr B A C) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr  ?D' ?F' ?E') (Tr A C B) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7
		| TCongruent (Tr  ?F' ?E'  ?D') (Tr C B A) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate7

		| TCongruent (Tr ?A' ?B' ?C') (Tr D E F) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?B' ?C' ?A') (Tr  E F D) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?C' ?A' ?B') (Tr  F D  E) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?B' ?A' ?C') (Tr E D F) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?A' ?C' ?B') (Tr  D F E) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr ?C' ?B' ?A') (Tr  F E  D) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr D E F) (Tr ?A' ?B' ?C') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr  E F D) (Tr ?B' ?C' ?A') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr  F D  E) (Tr ?C' ?A' ?B') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr E D F) (Tr ?B' ?A' ?C') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr  D F E) (Tr ?A' ?C' ?B') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
		| TCongruent (Tr  F E  D) (Tr ?C' ?B' ?A') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate7
	end
end.

Ltac stepTCongruent7 n := match n with
	| 1 => usingSSS7; try immediate6
	| 2 =>  usingSASa7; try immediate6
	| 3 => usingSASb7; try immediate6 
	| 4 =>  usingSASc7; try immediate6 
	| 5 =>  usingASAab7; try immediate6 
	| 6 => usingASAbc7; try immediate6
	| 7 =>  usingASAca7; try immediate6
	| _ => stepTCongruentTrans7 n
end.

Ltac stepCongruentAngle7 A B C D E F H :=  match type of H with
	| OpenRay B A D  => apply CongruentAngleSides; try immediate6
	| OpenRay B A F  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| OpenRay B C D  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| OpenRay B C F  => apply CongruentAngleSides; try immediate6
	| OpenRay B D A  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| OpenRay B F A  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| OpenRay B D C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| OpenRay B F C  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6

	| ClosedRay B A D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| ClosedRay B A F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| ClosedRay B C D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| ClosedRay B C F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| ClosedRay B D A  => apply CongruentAngleSides; try immediate6
	| ClosedRay B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| ClosedRay B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| ClosedRay B F C  => apply CongruentAngleSides; try immediate6

	| Segment B A D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| Segment B A F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment B C D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment B C F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| Segment B D A  => apply CongruentAngleSides; try immediate6
	| Segment B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment B F C  => apply CongruentAngleSides; try immediate6

	| Segment A B D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| Segment A B F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment C B D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment C B F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| Segment D B A  => apply CongruentAngleSides; try immediate6
	| Segment F B A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment D B C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Segment F B C  => apply CongruentAngleSides; try immediate6

	| Between B A D  =>apply CongruentAngleSides; try immediate6
	| Between B A F  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between B C D  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between B C F  =>apply CongruentAngleSides; try immediate6
	| Between B D A  => apply CongruentAngleSides; try immediate6
	| Between B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between B F C  => apply CongruentAngleSides; try immediate6

	| Between A D B  =>apply CongruentAngleSides; try immediate6
	| Between A F B  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between C D B  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between C F B  =>apply CongruentAngleSides; try immediate6
	| Between D A B  => apply CongruentAngleSides; try immediate6
	| Between F A B  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between D C B  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| Between F C B  => apply CongruentAngleSides; try immediate6

	| EquiOriented B A B D  => apply CongruentAngleSides; try immediate6
	| EquiOriented B A B F  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| EquiOriented B C B D  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| EquiOriented B C B F  => apply CongruentAngleSides; try immediate6
	| EquiOriented B D B A  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	| EquiOriented B F B A  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| EquiOriented B D B C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate6
	| EquiOriented B F B C  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate6
	
	| CongruentAngle _ _ _ _ _ _ => stepCongruentTransAngle6 A B C D E F H
	| NullAngle _ _ _ => apply (NullCongruentAngle A B C D E F) ; try immediate6
	| ElongatedAngle _ _ _  => apply (ElongatedCongruentAngle A B C D E F) ; try immediate6

	| TCongruent (Tr B A C)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle C B A M K L);
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr B C A)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle A B C M K L);
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr A B C)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle A B C K L M);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr C B A)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle C B A K L M);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr C A B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle A B C L M K);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr A C B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle C B A L M K);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr B A C) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle M K L C B A );
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr B C A) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle M K L A B C );
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr A B C) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle K L M A B C);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr C B A) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle K L M C B A);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr A C B)=> let Hyp := fresh in (
		assert (Hyp : CongruentAngle L M K C B A);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr C A B)=> let Hyp := fresh in (
		assert (Hyp : CongruentAngle L M K A B C);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| TCongruent (Tr E D F)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle F E D M K L);
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr E F D)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle D E F M K L);
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr D E F)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle D E F K L M);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr F E D)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle F E D K L M);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr D F E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle F E D L M K);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr F D E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle D E F L M K);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr E F D) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle M K L D E F );
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr E D F) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle M K L F E D );
		[ apply TCongruentAnglesA; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr D E F) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle K L M D E F);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr F E D) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle K L M F E D);
		[ apply TCongruentAnglesB; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr D F E)=> let Hyp := fresh in (
		assert (Hyp : CongruentAngle L M K F E D);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr F D E)=> let Hyp := fresh in (
		assert (Hyp : CongruentAngle L M K D E F);
		[ apply TCongruentAnglesC; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles1 (Tr A B C) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle A B C A C B);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr C B A) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle C B A C A B);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr A C B) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle A C B A B C);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr C A B) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle C A B C B A);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles2 (Tr B A C) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle A C B A B C);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr B C A) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle C A B C B A);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr A C B) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle C B A C A B);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr C A B) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle A B C A C B);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles3 (Tr B A C) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle C B A C A B);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr B C A) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle A B C A C B);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr A B C) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle C A B C B A);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr C B A) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle A C B A B C);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles1 (Tr D E F) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle D E F D F E);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr F E D) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle F E D F D E);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr D F E) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle D F E D E F);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr F D E) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle F D E F E D);
		[ apply IsoscelesEqAngles1; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles2 (Tr E D F) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle D F E D E F);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr E F D) => let Hyp := fresh in (
		assert (Hyp : CongruentAngle F D E F E D);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr D F E) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle F E D F D E);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr F D E) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle D E F D F E);
		[ apply IsoscelesEqAngles2; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles3 (Tr E D F) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle F E D F D E);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr E F D) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle D E F D F E);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr D E F) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle F D E F E D);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr F E D) =>let Hyp := fresh in (
		assert (Hyp : CongruentAngle D F E D E F);
		[ apply IsoscelesEqAngles3; try immediate7 | stepCongruentAngle7 A B C D E F Hyp])

	| Equilateral (Tr B A C) => assert (CongruentAngle A C B A B C);
		assert (CongruentAngle C B A C A B); try immediate7
	| Equilateral (Tr B C A) => assert (CongruentAngle C A B C B A);
		assert (CongruentAngle A B C A C B); try immediate7
	| Equilateral (Tr A B C) =>assert (CongruentAngle A B C A C B);
		assert (CongruentAngle C A B C B A); try immediate7
	| Equilateral (Tr C B A) =>assert (CongruentAngle C B A C A B);
		assert (CongruentAngle A C B A B C); try immediate7
	| Equilateral (Tr A C B) => assert ( CongruentAngle A C B A B C);
		assert (CongruentAngle C B A C A B); try immediate7
	| Equilateral (Tr C A B) => assert ( CongruentAngle C A B C B A);
		assert (CongruentAngle A B C A C B); try immediate7

	| Equilateral (Tr E D F) => assert (CongruentAngle D F E D E F);
		assert (CongruentAngle F E D F D E); try immediate7
	| Equilateral (Tr E F D) => assert (CongruentAngle F D E F E D);
		assert (CongruentAngle D E F D F E); try immediate7
	| Equilateral (Tr D E F) =>assert (CongruentAngle D E F D F E);
		assert (CongruentAngle F D E F E D); try immediate7
	| Equilateral (Tr F E D) =>assert (CongruentAngle F E D F D E);
		assert (CongruentAngle D F E D E F); try immediate7
	| Equilateral (Tr D F E) => assert ( CongruentAngle D F E D E F);
		assert (CongruentAngle F E D F D E); try immediate7
	| Equilateral (Tr F D E) => assert ( CongruentAngle F D E F E D);
		assert (CongruentAngle D E F D F E); try immediate7

	| ?X = ?Y => rewrite H || rewrite <- H

	
	| _ => eqToCongruent6; try immediate6
end.

Ltac step7 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance7 H
	| |- _ = DistancePlus _ _  => stepEqDistance7 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance7 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance7 H
	| |- Distance _ _ = _ => stepEqDistance7 H
	| |- _ = Distance _ _ => stepEqDistance7 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent6; try immediate7
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent6; try immediate7

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle7 A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle6 A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle6 A B C H

	| |- _ = H => try unfold H; byDefEqPoint5
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint5

	| |- ?A = ?B => stepEq6 A B H
	| |- ?A <> ?B => stepDistinct3 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct3 A B H

	| |- Collinear _ _ _  => stepCollinear6 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented1 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay6 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay6 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise3 A B C H
	| |- Between ?A ?B ?D => stepBetween6 A B D H
	| |- Segment ?A ?B ?C  => stepSegment1 A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec2 A B C D E F H

	| |- TStrict ?t => stepTStrict7 t H

	| |- TCongruent _ _ => stepTCongruent7 H

end.

Ltac since7 txt := assert txt; try immediate7.

Ltac from7 H txt := assert txt; [(step7 H; try immediate7) |  try immediate7].

Ltac as7 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate7 | (step7 Hyp ; try immediate7)]).

Ltac setEquilateral7 A B C := match goal with
	| H : A <> B |- _ => pose (C := ExistsClockwise A B H); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B H);
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B H); 
				fold C in Hyp, t))
	| H : B <> A |- _ => pose (C := ExistsClockwise A B (sym_not_eq H)); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B (sym_not_eq H)); 
				fold C in Hyp, t))
	| H : A = B -> False |- _ => pose (C := ExistsClockwise A B H); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B H);
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B H); 
				fold C in Hyp, t))
	| H : B = A -> False |- _ => pose (C := ExistsClockwise A B (sym_not_eq H)); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B (sym_not_eq H)); 
				fold C in Hyp, t))
	| _ => let H := fresh in (
			assert (H : A<> B) ; 
			[idtac | pose (C := ExistsClockwise A B H); 
				let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B H);
					let t := fresh "t"  in (
						assert (t := EquilateralExistsClockwise A B H); 
						fold C in Hyp, t))])
end.

Ltac setTCongruent7 A B C D E F := match goal with
	| Hab : A <> B, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))
	| Hab : A = B -> False, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))
	| Hba : B <> A, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))
	| Hba : B = A -> False, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))
	| Hab : A <> B  |- _ => let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate6 | pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))])
	| Hab : A = B -> False  |- _ => let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate6 | pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))])
	| Hba : B <> A  |- _ =>  let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate6 | pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))])
	| Hba : B = A -> False  |- _ =>  let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate6 | pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))])
	| _ => let Hab := fresh in 
			(assert (Hab : A<> B) ; 
			[try immediate6 |  let He := fresh in
				(assert (He :  Distance A B = Distance D E) ;
				[try immediate6 | pose (F := ThirdVertex A B C D E Hab He); 
					let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
						let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
							fold F in Hyp1, Hyp2))])])
end.

Ltac setTCongruentClockwise7 A B C D E F := match goal with
	| Hn : ~Collinear A B C, Hab : A <> B, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
				fold F in Hyp1, Hyp2))
	| Hn : ~Collinear A B C, Hba : B <> A, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E  (sym_not_eq Hba) He Hn); 
				fold F in Hyp1, Hyp2))
	| Hn : ~Collinear A B C, Hab : A <> B  |- _ => let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate6 | pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
				fold F in Hyp1, Hyp2))])
	| Hn : ~Collinear A B C, Hba : B <> A  |- _ =>  let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate6 | pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E  (sym_not_eq Hba) He Hn); 
				fold F in Hyp1, Hyp2))])
	| Hn : ~Collinear A B C  |- _ => let Hab := fresh in 
			(assert (Hab : A<> B) ; 
			[try immediate6 |  let He := fresh in
				(assert (He :  Distance A B = Distance D E) ;
				[try immediate6 | pose (F := ThirdVertex A B C D E Hab He); 
					let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
						let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
							fold F in Hyp1, Hyp2))])])
	| _ => let Hn := fresh in 
	(assert (Hn : ~Collinear A B C);
	[try immediate6 | let Hab := fresh in 
			(assert (Hab : A<> B) ; 
			[try immediate6 |  let He := fresh in
				(assert (He :  Distance A B = Distance D E) ;
				[try immediate6 | pose (F := ThirdVertex A B C D E Hab He); 
					let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
						let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
							fold F in Hyp1, Hyp2))])])])
end.

