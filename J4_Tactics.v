Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B6_EquiDirectedProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics .
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F4_ArchimedianDistance F5_Tactics .
Require Import G1_Angles G3_ParticularAngle G4_Tactics .
Require Import H1_Triangles H2_ParticularTriangles H4_Tactics .
Require Import I1_SupplementaryAngle I2_Supplement I3_OpposedAngles I4_Tactics .
Require Import J1_MidLine J2_MidPoint J3_MidProp.


Ltac immEquilateral9 := 
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

	| |- context [(MidLine ?A ?B ?H)] => let Hyp1 := fresh in let Hyp2 := fresh in (
		assert (Hyp1 := EquilateralAMidLineAB A B H);
		assert (Hyp2 := EquilateralBMidLineBA A B H);
		immEquilateral7)
end.

Ltac immBetween9 :=  match goal with
	| |- Between Uu Oo uU => exact BetweenUuOouU
	| |- Between uU Oo Uu => apply BetweenSym; exact BetweenUuOouU

	| H : Between ?A ?B ?C |- Between ?A ?B ?C => exact H
	| H : Between ?C ?B ?A |- Between ?A ?B ?C => apply (BetweenSym _ _ _ H)

	| |- Between ?C (FourPointsInterPoint _ _ ?C ?D _ _) ?D => apply FourPointsInterPointBetweenCD
	| |- Between ?D (FourPointsInterPoint _ _ ?C ?D _ _) ?C => apply BetweenSym; apply FourPointsInterPointBetweenCD

	| |- Between ?A ?B (SymmetricPoint ?A ?B _) => apply BetweenSymmetricPoint
	| |- Between  (SymmetricPoint ?A ?B _) ?B ?A => apply BetweenSym; apply BetweenSymmetricPoint

	| |- Between (Graduation ?n ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab) (Graduation (S (S ?n)) ?A ?B ?Hab) => apply GraduationBetweennSnSSn
	| |- Between (Graduation (S (S ?n)) ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab) (Graduation ?n ?A ?B ?Hab) => apply BetweenSym; apply GraduationBetweennSnSSn

	| H : ElongatedAngle ?B ?A ?C |- Between ?B ?A ?C => apply (ElongatedAngleBetween A B C H)
	| H : ElongatedAngle ?B ?A ?C |- Between ?C ?A ?B => apply BetweenSym; apply (ElongatedAngleBetween A B C H)

	| H : OpposedAngles ?A ?B _ ?C _ |- Between ?B ?A ?C => let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : OpposedAngles ?A ?B _ ?C _ |- Between ?C ?A ?B => apply BetweenSym; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : OpposedAngles ?A _ ?B _ ?C |- Between ?B ?A ?C => let Hyp := fresh in (inversion H as (_, Hyp); exact Hyp)
	| H : OpposedAngles ?A _ ?B _ ?C |- Between ?C ?A ?B => apply BetweenSym; let Hyp := fresh in (inversion H as (_, Hyp); exact Hyp)

	| |- Between ?A (MidPoint ?A ?B _ ) ?B => apply MidPointBetween
	| |- Between ?B (MidPoint ?A ?B _ ) ?A => apply BetweenSym; apply MidPointBetween
	| |- Between ?C (MidPoint ?A ?B _ ) ?D => apply MidPointBetweenMidLine || apply BetweenSym; apply MidPointBetweenMidLine

	| |- Between ?B _ _ => unfold B; immBetween6
	| |- Between _ ?B _ => unfold B; immBetween6
	| |- Between _ _ ?B => unfold B; immBetween6
end.

Ltac immSegment9 := match goal with
	| |- Segment ?A ?B ?A => apply SegmentABA
	| |- Segment ?A ?B ?B => apply SegmentABB
	| |- Segment Oo (DistancePlus?A ?B) ?A => apply IsDistanceSegmentDistancePlus; immIsDistance2 A

	| |- Segment (OppSegmentPoint ?A ?B _ _ _) ?B ?A => apply SegmentOppSegmentPoint
	| |- Segment ?B (OppSegmentPoint ?A ?B _ _ _) ?A => apply SegmentSym; apply SegmentOppSegmentPoint

	| |- Segment ?A (Graduation (S ?n) ?A _ _ ) (Graduation ?n ?A _ _) => apply GraduationSegment
	| |- Segment ?A (Graduation (S ?n) ?A ?B _ ) ?B => apply GraduationSegmentSn
	| |- Segment ?B (Graduation (S (S ?n)) ?A ?B _ ) (Graduation (S ?n) ?A ?B _) => apply GraduationSegmentB

	| H : Segment ?A ?B ?C |- Segment ?A ?B ?C => exact H
	| H : Segment ?A ?B ?C |- Segment ?B ?A ?C => apply (SegmentSym _ _ _ H)

	| H : EquiOriented ?A ?B ?B ?C |- Segment ?A ?C ?B => apply (EquiOrientedSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (EquiOrientedSegment A B C H)

	| |- Segment _ _ _  => apply BetweenSegment; immBetween9
	| |- Segment _ _ _  =>  apply SegmentSym; apply BetweenSegment ; immBetween9

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immCollinear9 := match goal with
	|  |- Collinear ?A ?A  _ => apply CollinearAAB	
	|  |- Collinear ?A _ ?A => apply CollinearABA	
	|  |- Collinear _ ?A ?A  => apply CollinearABB	

	|  |- Collinear Oo Uu (Distance _ _) => apply (ClosedRayCollinear _ _ _); apply IsDistanceDistance
	|  |- Collinear Oo (Distance _ _) Uu => apply CollinearACB; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistance
	|  |- Collinear Uu Oo (Distance _ _) => apply CollinearBAC; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistance
	|  |- Collinear Uu (Distance _ _) Oo => apply CollinearBCA; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistance
	|  |- Collinear (Distance _ _) Oo Uu => apply CollinearCAB; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistance
	|  |- Collinear (Distance _ _) Uu Oo => apply CollinearCBA; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistance

	|  |- Collinear Oo Uu (DistancePlus _ _) => apply (ClosedRayCollinear _ _ _); apply IsDistanceDistancePlus
	|  |- Collinear Oo (DistancePlus _ _) Uu => apply CollinearACB; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistancePlus
	|  |- Collinear Uu Oo (DistancePlus _ _) => apply CollinearBAC; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistancePlus
	|  |- Collinear Uu (DistancePlus _ _) Oo => apply CollinearBCA; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistancePlus
	|  |- Collinear (DistancePlus _ _) Oo Uu => apply CollinearCAB; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistancePlus
	|  |- Collinear (DistancePlus _ _) Uu Oo => apply CollinearCBA; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistancePlus

	|  |- Collinear Oo Uu (DistanceTimes _ _ _) => apply (ClosedRayCollinear _ _ _); apply IsDistanceDistanceTimes
	|  |- Collinear Oo (DistanceTimes _ _ _) Uu => apply CollinearACB; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistanceTimes
	|  |- Collinear Uu Oo (DistanceTimes _  _ _) => apply CollinearBAC; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistanceTimes
	|  |- Collinear Uu (DistanceTimes _ _ _) Oo => apply CollinearBCA; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistanceTimes
	|  |- Collinear (DistanceTimes _ _ _) Oo Uu => apply CollinearCAB; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistanceTimes
	|  |- Collinear (DistanceTimes _ _ _) Uu Oo => apply CollinearCBA; apply (ClosedRayCollinear _ _ _); apply IsDistanceDistanceTimes

	| H : Collinear ?A ?B ?C |- Collinear ?A ?B ?C => exact H	
	| H : Collinear ?A ?B ?C |- Collinear ?A ?C ?B => apply (CollinearACB _ _ _ H)
	| H : Collinear ?A ?B ?C |- Collinear ?B ?A ?C => apply (CollinearBAC _ _ _ H)
	| H : Collinear ?A ?B ?C |- Collinear ?B ?C ?A => apply (CollinearBCA _ _ _ H)
	| H : Collinear ?A ?B ?C |- Collinear ?C ?A ?B => apply (CollinearCAB _ _ _ H)
	| H : Collinear ?A ?B ?C |- Collinear ?C ?B ?A => apply (CollinearCBA _ _ _ H)

	| H : EquiOriented ?A ?B ?C ?B |- Collinear ?A ?B ?C => apply (EquiOrientedCollinearCB _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?B |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiOrientedCollinearCB _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?B |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiOrientedCollinearCB _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?B |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiOrientedCollinearCB _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?B |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiOrientedCollinearCB _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?B |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiOrientedCollinearCB _ _ _ H)

	| H : EquiOriented ?A ?B ?C ?A |- Collinear ?A ?B ?C => apply (EquiOrientedCollinearCA _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiOrientedCollinearCA _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiOrientedCollinearCA _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiOrientedCollinearCA _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiOrientedCollinearCA _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiOrientedCollinearCA _ _ _ H)

	| H : EquiOriented ?A ?B ?B ?C |- Collinear ?A ?B ?C => apply (EquiOrientedCollinearBC _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiOrientedCollinearBC _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiOrientedCollinearBC _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiOrientedCollinearBC _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiOrientedCollinearBC _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiOrientedCollinearBC _ _ _ H)

	| H : EquiOriented ?A ?B ?A ?C |- Collinear ?A ?B ?C => apply (EquiOrientedCollinearAC _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiOrientedCollinearAC _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiOrientedCollinearAC _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiOrientedCollinearAC _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiOrientedCollinearAC _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiOrientedCollinearAC _ _ _ H)

	| H : OpenRay ?A ?B ?C |- Collinear ?A ?B ?C => apply (OpenRayCollinear _ _ _ H)
	| H : OpenRay ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (OpenRayCollinear _ _ _ H)
	| H : OpenRay ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (OpenRayCollinear _ _ _ H)
	| H : OpenRay ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (OpenRayCollinear _ _ _ H)
	| H : OpenRay ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (OpenRayCollinear _ _ _ H)
	| H : OpenRay ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (OpenRayCollinear _ _ _ H)

	| H : ClosedRay ?A ?B ?C |- Collinear ?A ?B ?C => apply (ClosedRayCollinear _ _ _ H)
	| H : ClosedRay ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (ClosedRayCollinear _ _ _ H)
	| H : ClosedRay ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (ClosedRayCollinear _ _ _ H)
	| H : ClosedRay ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (ClosedRayCollinear _ _ _ H)
	| H : ClosedRay ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (ClosedRayCollinear _ _ _ H)
	| H : ClosedRay ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (ClosedRayCollinear _ _ _ H)

	| H : Between ?A ?B ?C |- Collinear ?A ?B ?C => apply (BetweenCollinear _ _ _ H)
	| H : Between ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (BetweenCollinear _ _ _ H)
	| H : Between ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (BetweenCollinear _ _ _ H)
	| H : Between ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (BetweenCollinear _ _ _ H)
	| H : Between ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (BetweenCollinear _ _ _ H)
	| H : Between ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (BetweenCollinear _ _ _ H)

	| H : Segment ?A ?C ?B |- Collinear ?A ?B ?C => apply (SegmentCollinear _ _ _ H)
	| H : Segment ?A ?C ?B |- Collinear ?A ?C ?B => apply CollinearACB; apply (SegmentCollinear _ _ _ H)
	| H : Segment ?A ?C ?B |- Collinear ?B ?A ?C => apply CollinearBAC; apply (SegmentCollinear _ _ _ H)
	| H : Segment ?A ?C ?B |- Collinear ?B ?C ?A => apply CollinearBCA; apply (SegmentCollinear _ _ _ H)
	| H : Segment ?A ?C ?B |- Collinear ?C ?A ?B => apply CollinearCAB; apply (SegmentCollinear _ _ _ H)
	| H : Segment ?A ?C ?B |- Collinear ?C ?B ?A => apply CollinearCBA; apply (SegmentCollinear _ _ _ H)

	| H : EquiDirected ?A ?B ?C ?A |- Collinear ?A ?B ?C => apply (EquiDirectedCollinear _ _ _ H)
	| H : EquiDirected ?A ?B ?C ?A |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiDirectedCollinear _ _ _ H)
	| H : EquiDirected ?A ?B ?C ?A |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiDirectedCollinear _ _ _ H)
	| H : EquiDirected ?A ?B ?C ?A |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiDirectedCollinear _ _ _ H)
	| H : EquiDirected ?A ?B ?C ?A |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiDirectedCollinear _ _ _ H)
	| H : EquiDirected ?A ?B ?C ?A |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiDirectedCollinear _ _ _ H)

	| H : EquiDirected ?B ?A ?C ?A |- Collinear ?A ?B ?C => apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutAB _ _ _ _ H))
	| H : EquiDirected ?B ?A ?C ?A |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutAB _ _ _ _ H))
	| H : EquiDirected ?B ?A ?C ?A |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutAB _ _ _ _ H))
	| H : EquiDirected ?B ?A ?C ?A |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutAB _ _ _ _ H))
	| H : EquiDirected ?B ?A ?C ?A |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutAB _ _ _ _ H))
	| H : EquiDirected ?B ?A ?C ?A |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutAB _ _ _ _ H))

	| H : EquiDirected ?A ?B ?A ?C |- Collinear ?A ?B ?C => apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutCD _ _ _ _ H))
	| H : EquiDirected ?A ?B ?A ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutCD _ _ _ _ H))
	| H : EquiDirected ?A ?B ?A ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutCD _ _ _ _ H))
	| H : EquiDirected ?A ?B ?A ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutCD _ _ _ _ H))
	| H : EquiDirected ?A ?B ?A ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutCD _ _ _ _ H))
	| H : EquiDirected ?A ?B ?A ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiDirectedCollinear _ _ _ (EquiDirectedPermutCD _ _ _ _ H))

	| H : EquiDirected ?C ?A ?A ?B |- Collinear ?A ?B ?C => apply (EquiDirectedCollinear _ _ _ (EquiDirectedSym _ _ _ _ H))
	| H : EquiDirected ?C ?A ?A ?B |- Collinear ?A ?C ?B => apply CollinearACB; apply (EquiDirectedCollinear _ _ _ (EquiDirectedSym _ _ _ _ H))
	| H : EquiDirected ?C ?A ?A ?B |- Collinear ?B ?A ?C => apply CollinearBAC; apply (EquiDirectedCollinear _ _ _ (EquiDirectedSym _ _ _ _ H))
	| H : EquiDirected ?C ?A ?A ?B |- Collinear ?B ?C ?A => apply CollinearBCA; apply (EquiDirectedCollinear _ _ _ (EquiDirectedSym _ _ _ _ H))
	| H : EquiDirected ?C ?A ?A ?B |- Collinear ?C ?A ?B => apply CollinearCAB; apply (EquiDirectedCollinear _ _ _ (EquiDirectedSym _ _ _ _ H))
	| H : EquiDirected ?C ?A ?A ?B |- Collinear ?C ?B ?A => apply CollinearCBA; apply (EquiDirectedCollinear _ _ _ (EquiDirectedSym _ _ _ _ H))

	| H : Archimed ?A ?B ?C |- Collinear ?A ?B ?C => apply (ClosedRayCollinear _ _ _); apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply (ClosedRayCollinear _ _ _); apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply (ClosedRayCollinear _ _ _); apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply (ClosedRayCollinear _ _ _); apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply (ClosedRayCollinear _ _ _); apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply (ClosedRayCollinear _ _ _); apply (ArchimedianClosedRay _ _ _ H)

	| H : OnLine (Ruler ?A ?B _) ?C |- Collinear ?A ?B ?C => exact H
	| H : OnLine (Ruler ?A ?B _) ?C |- Collinear ?A ?C ?B => apply CollinearACB; exact H
	| H : OnLine (Ruler ?A ?B _) ?C |- Collinear ?B ?A ?C => apply CollinearBAC; exact H
	| H : OnLine (Ruler ?A ?B _) ?C |- Collinear ?B ?C ?A => apply CollinearBCA; exact H
	| H : OnLine (Ruler ?A ?B _) ?C |- Collinear ?C ?A ?B =>  apply CollinearCAB; exact H
	| H : OnLine (Ruler ?A ?B _) ?C |- Collinear ?C ?B ?A => apply CollinearCBA; exact H

	| H : OnLine ?d ?C |- Collinear ?A ?B ?C => destruct d; exact H
	| H : OnLine ?d ?C |- Collinear ?A ?C ?B => destruct d; apply CollinearACB; exact H
	| H : OnLine ?d ?C |- Collinear ?B ?A ?C => destruct d; apply CollinearBAC; exact H
	| H : OnLine ?d ?C |- Collinear ?B ?C ?A => destruct d; apply CollinearBCA; exact H
	| H : OnLine ?d ?C |- Collinear ?C ?A ?B => destruct d; apply CollinearCAB; exact H
	| H : OnLine ?d ?C |- Collinear ?C ?B ?A => destruct d; apply CollinearCBA; exact H

	| H : NullAngle ?B ?A ?C |- Collinear ?A ?B ?C => apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)

	| H : ElongatedAngle ?A ?B ?C |- Collinear ?A ?B ?C => apply BetweenCollinear; apply (ElongatedAngleBetween A B C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply BetweenCollinear; apply (ElongatedAngleBetween A B C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply BetweenCollinear; apply (ElongatedAngleBetween A B C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply BetweenCollinear; apply (ElongatedAngleBetween A B C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply BetweenCollinear; apply (ElongatedAngleBetween A B C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply BetweenCollinear; apply (ElongatedAngleBetween A B C H)

	| |- Collinear ?A ?B (FourPointsInterPoint ?A ?B _ _ _ _) => apply FourPointsInterPointCollinearAB
	| |- Collinear ?B ?A (FourPointsInterPoint ?A ?B _ _ _ _) => apply CollinearBAC; apply FourPointsInterPointCollinearAB
	| |- Collinear ?A (FourPointsInterPoint ?A ?B _ _ _ _) ?B => apply CollinearACB; apply FourPointsInterPointCollinearAB
	| |- Collinear ?B (FourPointsInterPoint ?A ?B _ _ _ _) ?A => apply CollinearBCA; apply FourPointsInterPointCollinearAB
	| |- Collinear (FourPointsInterPoint ?A ?B _ _ _ _) ?A ?B => apply CollinearCAB; apply FourPointsInterPointCollinearAB
	| |- Collinear (FourPointsInterPoint ?A ?B _ _ _ _) ?B  ?A => apply CollinearCBA; apply FourPointsInterPointCollinearAB

	| |- Collinear ?C ?D (FourPointsInterPoint _ _ ?C ?D _ _) => apply CollinearACB; apply BetweenCollinear; apply FourPointsInterPointBetweenCD
	| |- Collinear ?D ?C (FourPointsInterPoint _ _ ?C ?D _ _) => apply CollinearCAB; apply BetweenCollinear; apply FourPointsInterPointBetweenCD
	| |- Collinear ?C (FourPointsInterPoint _ _ ?C ?D _ _) ?D => apply BetweenCollinear; apply FourPointsInterPointBetweenCD
	| |- Collinear ?D (FourPointsInterPoint _ _ ?C ?D _ _) ?C => apply CollinearCBA; apply BetweenCollinear; apply FourPointsInterPointBetweenCD
	| |- Collinear (FourPointsInterPoint _ _ ?C ?D _ _) ?C ?D => apply CollinearBAC; apply BetweenCollinear; apply FourPointsInterPointBetweenCD
	| |- Collinear (FourPointsInterPoint _ _ ?C ?D _ _) ?D  ?C => apply CollinearBCA; apply BetweenCollinear; apply FourPointsInterPointBetweenCD

	| |- Collinear ?A ?B (NotEquiDirectedInterPoint ?A ?B _ _ _ _) => apply NotEquiDirectedInterPointCollinearAB
	| |- Collinear ?B ?A (NotEquiDirectedInterPoint ?A ?B _ _ _ _) => apply CollinearBAC; apply NotEquiDirectedInterPointCollinearAB
	| |- Collinear ?A (NotEquiDirectedInterPoint ?A ?B _ _ _ _) ?B => apply CollinearACB; apply NotEquiDirectedInterPointCollinearAB
	| |- Collinear ?B (NotEquiDirectedInterPoint ?A ?B _ _ _ _) ?A => apply CollinearBCA; apply NotEquiDirectedInterPointCollinearAB
	| |- Collinear (NotEquiDirectedInterPoint ?A ?B _ _ _ _) ?A ?B => apply CollinearCAB; apply NotEquiDirectedInterPointCollinearAB
	| |- Collinear (NotEquiDirectedInterPoint ?A ?B _ _ _ _) ?B  ?A => apply CollinearCBA; apply NotEquiDirectedInterPointCollinearAB

	| |- Collinear ?C ?D (NotEquiDirectedInterPoint _ _ ?C ?D _ _) => apply NotEquiDirectedInterPointCollinearCD
	| |- Collinear ?D ?C (NotEquiDirectedInterPoint _ _ ?C ?D _ _) => apply CollinearBAC; apply NotEquiDirectedInterPointCollinearCD
	| |- Collinear ?C (NotEquiDirectedInterPoint _ _ ?C ?D _ _) ?D => apply CollinearACB; apply NotEquiDirectedInterPointCollinearCD
	| |- Collinear ?D (NotEquiDirectedInterPoint _ _ ?C ?D _ _) ?C => apply CollinearBCA; apply NotEquiDirectedInterPointCollinearCD
	| |- Collinear (NotEquiDirectedInterPoint _ _ ?C ?D _ _) ?C ?D => apply CollinearCAB; apply NotEquiDirectedInterPointCollinearCD
	| |- Collinear (NotEquiDirectedInterPoint _ _ ?C ?D _ _) ?D  ?C => apply CollinearCBA; apply NotEquiDirectedInterPointCollinearCD

	| |- Collinear (InterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immCollinear4
	| |- Collinear _ (InterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immCollinear4
	| |- Collinear _ _ (InterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immCollinear4

	| |- Collinear (SecondInterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immCollinear4
	| |- Collinear _ (SecondInterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immCollinear4
	| |- Collinear _ _ (SecondInterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immCollinear4

	| |- Collinear (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := CollinearAddSegmentPoint A B C D E H H0); immCollinear4
	| |- Collinear _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ => let Hyp := fresh in assert (Hyp := CollinearAddSegmentPoint A B C D E H H0); immCollinear4
	| |- Collinear _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) => let Hyp := fresh in assert (Hyp := CollinearAddSegmentPoint A B C D E H H0); immCollinear4

	| |- Collinear (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immCollinear4
	| |- Collinear _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immCollinear4
	| |- Collinear _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immCollinear4

	| |- Collinear (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immCollinear4
	| |- Collinear _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immCollinear4
	| |- Collinear _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immCollinear4

	| |- Collinear (SymmetricPoint ?A ?B ?H) _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immCollinear4
	| |- Collinear _ (SymmetricPoint ?A ?B ?H) _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immCollinear4
	| |- Collinear _ _ (SymmetricPoint ?A ?B ?H) => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immCollinear4

	| |- Collinear (MidPoint ?A ?B ?H) _ _ => apply CollinearCAB; apply (MidPointCollinearAB A B H)
	| |- Collinear _ (MidPoint ?A ?B ?H) _ => apply CollinearACB; apply (MidPointCollinearAB A B H)
	| |- Collinear _ _ (MidPoint ?A ?B ?H) =>  apply (MidPointCollinearAB A B H)

	| |- Collinear ?A ?B (Graduation _ ?A ?B _ ) => apply CollinearGraduation
	| |- Collinear ?B ?A (Graduation _ ?A ?B _ ) => apply CollinearBAC; apply CollinearGraduation
	| |- Collinear ?A (Graduation _ ?A ?B _ ) ?B => apply CollinearACB; apply CollinearGraduation
	| |- Collinear ?B (Graduation _ ?A ?B _ ) ?A => apply CollinearBCA; apply CollinearGraduation
	| |- Collinear (Graduation _ ?A ?B _ ) ?A ?B => apply CollinearCAB; apply CollinearGraduation
	| |- Collinear (Graduation _ ?A ?B _ ) ?B  ?A => apply CollinearCBA; apply CollinearGraduation

	| |- Collinear ?A _ _ => unfold A; immCollinear4
	| |- Collinear _ ?B _ => unfold B; immCollinear4
	| |- Collinear _ _ ?C => unfold C; immCollinear4
end.

Ltac immClockwise9 := match goal with
	| H : Clockwise ?A ?B ?C |- Clockwise ?A ?B ?C => exact H	
	| H : Clockwise ?A ?B ?C |- Clockwise ?B ?C ?A => exact (ClockwiseBCA A B C H)
	| H : Clockwise ?A ?B ?C |- Clockwise ?C ?A ?B => exact (ClockwiseCAB A B C H)

	| |- Clockwise  ?A (LineA (MidLine ?A ?B _)) ?B => apply ClockwiseAMidLineAB
	| |- Clockwise  (LineA (MidLine ?A ?B _)) ?B ?A => apply ClockwiseBCA; apply ClockwiseAMidLineAB
	| |- Clockwise ?B  ?A (LineA (MidLine ?A ?B _)) => apply ClockwiseCAB;apply ClockwiseAMidLineAB

	| |- Clockwise ?B (LineB (MidLine ?A ?B _)) ?A => apply ClockwiseBMidLineBA
	| |- Clockwise (LineB (MidLine ?A ?B _)) ?A ?B => apply ClockwiseBCA; apply ClockwiseBMidLineBA
	| |- Clockwise ?A ?B (LineB (MidLine ?A ?B _)) => apply ClockwiseCAB; apply ClockwiseBMidLineBA

	| |- Clockwise ?A (LineA (MidLine ?A ?B ?H)) (MidPoint ?A ?B ?H) => apply ClockwiseAMidLineAMidPoint
	| |- Clockwise (LineA (MidLine ?A ?B ?H)) (MidPoint ?A ?B ?H) ?A => apply ClockwiseBCA; apply ClockwiseAMidLineAMidPoint
	| |- Clockwise (MidPoint ?A ?B ?H) ?A (LineA (MidLine ?A ?B ?H)) => apply ClockwiseCAB; apply ClockwiseAMidLineAMidPoint

	| |- Clockwise (LineA (MidLine ?A ?B ?H)) ?B (MidPoint ?A ?B ?H) => apply ClockwiseMidLineABMidPoint
	| |- Clockwise ?B (MidPoint ?A ?B ?H) (LineA (MidLine ?A ?B ?H)) => apply ClockwiseBCA; apply ClockwiseMidLineABMidPoint
	| |- Clockwise (MidPoint ?A ?B ?H) (LineA (MidLine ?A ?B ?H)) ?B => apply ClockwiseCAB; apply ClockwiseMidLineABMidPoint

	| |- Clockwise ?A (LineA (MidLine ?A ?B ?H)) (LineB (MidLine ?A ?B ?H)) => apply ClockwiseAMidLineAMidLineB
	| |- Clockwise (LineA (MidLine ?A ?B ?H)) (LineB (MidLine ?A ?B ?H)) ?A => apply ClockwiseBCA; apply ClockwiseAMidLineAMidLineB
	| |- Clockwise (LineB (MidLine ?A ?B ?H)) ?A (LineA (MidLine ?A ?B ?H)) => apply ClockwiseCAB; apply ClockwiseAMidLineAMidLineB

	| |- Clockwise ?B (LineB (MidLine ?A ?B ?H)) (LineA (MidLine ?A ?B ?H)) => apply ClockwiseBMidLineBMidLineA
	| |- Clockwise (LineB (MidLine ?A ?B ?H)) (LineA (MidLine ?A ?B ?H)) ?B => apply ClockwiseBCA; apply ClockwiseBMidLineBMidLineA
	| |- Clockwise  (LineA (MidLine ?A ?B ?H)) ?B (LineB (MidLine ?A ?B ?H))=> apply ClockwiseCAB; apply ClockwiseBMidLineBMidLineA

	| H : EquiOriented (LineA (MidLine ?A ?B ?Hab)) (LineB (MidLine ?A ?B ?Hab)) (MidPoint ?A ?B ?Hab)  ?M |-Clockwise ?A ?B ?M => apply (EquiOrientedMidLineClockwiseAB A B M Hab H)
	| H : EquiOriented (LineA (MidLine ?A ?B ?Hab)) (LineB (MidLine ?A ?B ?Hab)) (MidPoint ?A ?B ?Hab)  ?M |-Clockwise ?B ?M ?A=> apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseAB A B M Hab H)
	| H : EquiOriented (LineA (MidLine ?A ?B ?Hab)) (LineB (MidLine ?A ?B ?Hab)) (MidPoint ?A ?B ?Hab)  ?M |-Clockwise ?M ?A ?B => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseAB A B M Hab H)

	| H : EquiOriented (LineB (MidLine ?A ?B ?Hab)) (LineA (MidLine ?A ?B ?Hab)) (MidPoint ?A ?B ?Hab)  ?M |-Clockwise ?A ?M ?B => apply (EquiOrientedMidLineClockwiseBA A B M Hab H)
	| H : EquiOriented (LineB (MidLine ?A ?B ?Hab)) (LineA (MidLine ?A ?B ?Hab)) (MidPoint ?A ?B ?Hab)  ?M |-Clockwise ?M ?B ?A =>  apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseBA A B M Hab H)
	| H : EquiOriented (LineB (MidLine ?A ?B ?Hab)) (LineA (MidLine ?A ?B ?Hab)) (MidPoint ?A ?B ?Hab)  ?M |-Clockwise ?B ?A ?M => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseBA A B M Hab H)
end.

Ltac immNotClockwise9 := match goal with
	|  |- ~Clockwise ?A ?A _ => apply NotClockwiseAAB	
	|  |- ~Clockwise ?A _ ?A => apply NotClockwiseABA
	|  |- ~Clockwise _ ?A ?A => apply NotClockwiseABB

	| |- ~Clockwise _ (IntersectionCirclesPoint ?c1 ?c2 ?H) _ => let Hyp := fresh in (
					assert (Hyp := NotClockwiseIntersectionCirclesPoint c1 c2 H);
					simplCircle1; exact Hyp)

	|   |- ~Clockwise (Angle ?A ?B ?C ?H1 ?H2) Oo Uu => let Hyp := fresh in assert (Hyp := NotClockwiseAngle A B C H1 H2); immNotClockwise3
	|   |- ~Clockwise Oo Uu (Angle ?A ?B ?C ?H1 ?H2) => let Hyp := fresh in assert (Hyp := NotClockwiseAngle A B C H1 H2); immNotClockwise3
	|   |- ~Clockwise Uu (Angle ?A ?B ?C ?H1 ?H2) Oo => let Hyp := fresh in assert (Hyp := NotClockwiseAngle A B C H1 H2); immNotClockwise3

	| H : IsAngle ?A  |- ~Clockwise ?A Oo Uu => destruct H; immNotClockwise3
	| H : IsAngle ?A  |- ~Clockwise Oo Uu ?A => destruct H; immNotClockwise3
	| H : IsAngle ?A  |- ~Clockwise Uu ?A Oo => destruct H; immNotClockwise3

	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?A ?B ?C => exact H	
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?B ?C ?A => intro; elim H; immClockwise9
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?C ?A ?B => intro; elim H; immClockwise9

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?D => apply (EquiOrientedNotClockwiseABD _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?D ?A => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise9
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?D ?A ?B => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise9

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?C => apply (EquiOrientedNotClockwiseABC _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?C ?A => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise9
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?C ?A ?B => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise9

	|  |- ~Clockwise ?A ?B ?C => apply ClockwiseNotClockwise; immClockwise9
	|  |- ~Clockwise ?A ?B ?C => apply CollinearNotClockwise; immCollinear9 
end.

Ltac immDistinct9 := match goal with
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

	| |- MidPoint ?A _ _ <> ?A => apply DistinctMidPointA
	| |- ?A <> MidPoint ?A _ _  => apply sym_not_eq; apply DistinctMidPointA
	| |- MidPoint _ ?B _  <> ?B => apply DistinctMidPointB
	| |- ?B <> MidPoint _ ?B _   => apply sym_not_eq; apply DistinctMidPointB

	| |- MidPoint ?A ?B ?H <> LineA (MidLine ?A ?B ?H) => apply MidPointDistinctMidLineA
	| |- LineA (MidLine ?A ?B ?H) <> MidPoint ?A ?B ?H => apply sym_not_eq; apply MidPointDistinctMidLineA
	| |- MidPoint ?A ?B ?H <> LineB (MidLine ?A ?B ?H) => apply MidPointDistinctMidLineB
	| |- LineB (MidLine ?A ?B ?H) <> MidPoint ?A ?B ?H => apply sym_not_eq; apply MidPointDistinctMidLineB

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

	| H : Supplement ?A ?B _ _ _ _ |- ?B <> ?A => inversion H; immDistinct1
	| H : Supplement ?A ?B _ _ _ _ |- ?A <> ?B => inversion H; immDistinct1
	| H : Supplement _ ?B ?C _ _ _ |- ?B <> ?C => inversion H; immDistinct1
	| H : Supplement _ ?B ?C _ _ _ |- ?C <> ?B => inversion H; immDistinct1
	| H : Supplement _ _ _ ?D ?E _ |- ?E <> ?D => inversion H; immDistinct1
	| H : Supplement _ _ _ ?D ?E _ |- ?D <> ?E => inversion H; immDistinct1
	| H : Supplement _ _ _ _  ?E ?F |- ?E <> ?F => inversion H; immDistinct1
	| H : Supplement _ _ _ _  ?E ?F |- ?F <> ?E => inversion H; immDistinct1

	| H : OpposedAngles ?A ?B _ _ _ |- ?B <> ?A => inversion H; immDistinct3
	| H : OpposedAngles ?A ?B _ _ _ |- ?A <> ?B => inversion H; immDistinct3
	| H : OpposedAngles ?B _ ?C _ _ |- ?B <> ?C => inversion H; immDistinct3
	| H : OpposedAngles ?B _ ?C _ _ |- ?C <> ?B => inversion H; immDistinct3
	| H : OpposedAngles ?D _ _ ?E _ |- ?E <> ?D => inversion H; immDistinct3
	| H : OpposedAngles ?D _ _ ?E _ |- ?D <> ?E => inversion H; immDistinct3
	| H : OpposedAngles ?E _ _ _ ?F |- ?E <> ?F => inversion H; immDistinct3
	| H : OpposedAngles ?E _ _ _ ?F |- ?F <> ?E => inversion H; immDistinct3
end.

Ltac solveEq9 := match goal with
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

Ltac generalizeMid9 := repeat match goal with 
	| |- context[MidPoint ?A ?B ?H] => generalize (MidPointEqDistance A B H); let J := fresh in (pose (J := MidPoint A B H); fold J)
end.

Ltac solveDist9 :=try solveOnCircleDist2; try generalizeMid9; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2;  unfoldDistance2; solveEq2.

Ltac solveDistPlus9 := try generalizeMid9; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistancePlus2; unfoldDistancePlus2; substDistancePlus2; solveEq2.

Ltac solveDistTimes9 := try generalizeMid9; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistanceTimes2; unfoldDistanceTimes2; substDistanceTimes2; solveEq2.

Ltac solveDistance9 := simplDistance8; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus9
	| |- _ = DistancePlus _ _ => solveDistPlus9

	| |- DistanceTimes _ _ _ = _ => solveDistTimes9
	| |- _ = DistanceTimes _ _ _ => solveDistTimes9

	| |- Distance _ _ = _ => solveDist9
	| |- _ = Distance _ _ => apply sym_eq; solveDist9

	| |- _ => solveEq9
end.

Ltac immOnLine9 := match goal with
	| H : OnLine ?d ?A |- OnLine ?d ?A => exact H
	| |- OnLine ?d (LineA ?d) => destruct d; simpl; immediate4
	| |- OnLine ?d (LineB ?d) => destruct d; simpl; immediate4

	| |- OnLine ?d (InterLinesPoint ?d _ _) => apply OnLine1InterLinesPoint
	| |- OnLine ?d (InterLinesPoint _ ?d _) => apply OnLine2InterLinesPoint
	| |- OnLine ?d (InterDiameterPoint ?d _ _) => apply OnLineInterDiameterPoint
	| |- OnLine ?d (SecondInterDiameterPoint ?d _ _) => apply OnLineSecondInterDiameterPoint

	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?A ?B ?H) => apply MidPointOnMidLine
	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?A ?B ?H') => rewrite (MidPointRefl A B H' H); apply MidPointOnMidLine
	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?B ?A ?H') =>  rewrite (MidPointSym B A H' H); apply MidPointOnMidLine

	| |- OnLine (MidLine ?A ?B ?H) ?M => apply EqDistanceOnMidLine; solveDist9

	| |- OnLine (Ruler _ _ _) _ => simpl; immediate4
	| |- OnLine ?d _ => unfold d; simpl; immediate4
end.

Ltac immTCongruent9 := match goal with
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

	| |- TCongruent ?t1 _ => unfold t1; immTCongruent9
	| |- TCongruent _ ?t2 => unfold t2; immTCongruent9

	| |- context [(MidLine ?A ?B ?Hab)] => let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in let Hyp4 := fresh in let Hyp5 := fresh in
 		assert (Hyp1 := (TCongruentMidLineAMidLineB A B Hab));
		assert (Hyp2 := (TCongruentAIA'BIA' A B Hab));
		assert (Hyp3 := (TCongruentAIB'BIB' A B Hab));
		assert (Hyp4 := (TCongruentAIA'AIB' A B Hab));
		assert (Hyp5 := (TCongruentBIA'BIB' A B Hab));
		immTCongruent7
	
	| _ => solve [usingSSS7; immediate8
				| usingSASa7; immediate8
				| usingSASb7; immediate8 
				| usingSASc7; immediate8
				| usingASAab7; immediate8 
				| usingASAbc7; immediate8
				| usingASAca7; immediate8]
	
end.

Ltac immediate9 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate9
	| |- ?A \/ ?B => (left; immediate9)  || (right; immediate9)

	| |- DistancePlus _ _ = _ => solveDistance9
	| |- _ = DistancePlus _ _ => solveDistance9

	| |- DistanceTimes _ _ _ = _ => solveDistance9
	| |- _ = DistanceTimes _ _ _ => solveDistance9

	| |- Distance _ _ = _ => solveDistance9
	| |- _ = Distance _ _ => solveDistance9

	| |- IsDistance ?d => immIsDistance2 d

	| |- Supplementary _ _ = _ => solveSupplementary8 || (apply SupplementarySym; solveSupplementary8)
	| |- _ = Supplementary _ _ => solveSupplementary8 || (apply SupplementarySym; solveSupplementary8)

	| |-  Supplement _ _ _ _ _ _ => immSupplement8 
	| |-  OpposedAngles _ _ _ _ _ =>  apply OpposedAngleDef; immBetween8 

	| |- Angle _ _ _ _ _ = _ => solveAngle8
	| |-  _ = Angle _ _ _ _ _ => solveAngle8

	| |- CongruentAngle _ _ _ _ _ _ => immCongruentAngle8
	| |- NullAngle _ _ _ => immNullAngle6
	| |- ElongatedAngle _ _ _ => immElongatedAngle6
	| |- ~NullAngle _ _ _ => immNotNullAngle6
	| |- ~ElongatedAngle _ _ _ => immNotElongatedAngle6

	| |- IsAngle _ => immIsAngle8

	| |- _ = _ => solveEq9
	| |- _ <> _ => immDistinct9
	| |- ?A = ?B -> False => fold(A <> B); immDistinct9

	| |- Clockwise _ _ _ => immClockwise9
	| |- ~Clockwise _ _ _  => immNotClockwise9
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise9

	| |- Collinear _ _ _ => immCollinear9
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1

	| |- EquiOriented _ _ _ _ => immEquiOriented5
	| |- OpenRay _ _ _ => immOpenRay6
	| |- ClosedRay _ _ _ => immClosedRay6
	| |- Between _ _ _ => immBetween9
	| |- Segment _ _ _ => immSegment9

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
	| |- OnLine _ _ => immOnLine9

	| |- TStrict _ => immTStrict7
	| |- Isosceles1 ?t => unfold t; immIsoscelesOne7
	| |- Isosceles1 (Tr _ _ _) => immIsoscelesOne7
	| |- Isosceles2 ?t => unfold t; immIsoscelesTwo7
	| |- Isosceles2 (Tr _ _ _) => immIsoscelesTwo7
	| |- Isosceles3 ?t => unfold t; immIsoscelesThree7
	| |- Isosceles3 (Tr _ _ _) => immIsoscelesThree7
	| |- Equilateral ?t => unfold t; immEquilateral9
	| |- Equilateral (Tr _ _ _) => immEquilateral9

	| |- TCongruent _ _ => immTCongruent9
end.

Ltac byDefEqPoint9 := match goal with
	| |- ?X = ?X => apply refl_equal

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
end.

Ltac stepEqDistance9 H  := 
 repeat rewrite <- DistancePlusAssoc;
 repeat rewrite <- DistancePlusAssoc in H;
match type of H with
	| DistancePlus _ _  = _ => foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| _ = DistancePlus _ _  => foldDistanceIn2 H;  foldDistanceTimesIn2 H; foldDistancePlusIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H; unfoldDistancePlusIn2 H
	| DistanceTimes _ _ _  = _ => foldDistanceTimesIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| _ = DistanceTimes _ _ _  => foldDistanceTimesIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| Distance _ _ = _ => foldDistanceIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H
	| _ = Distance _ _ => foldDistanceIn2 H; substDistanceIn2 H; unfoldDistanceIn2 H

	| OnLine (MidLine ?A ?B ?Hab) ?C => generalize (OnMidLineEqDistance A B Hab C H); intro

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

end; try immediate7.

Ltac stepClockwise9 A B C H := match type of H with

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

	| context [(MidLine A B ?H1)] => apply (EquiOrientedMidLineClockwiseAB A B C H1); try immediate9
	| context [(MidPoint A B ?H1)] => apply (EquiOrientedMidLineClockwiseAB A B C H1); try immediate9
	| context [(MidLine B C ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseAB B C A H1); try immediate9
	| context [(MidPoint B C ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseAB B C A H1); try immediate9
	| context [(MidLine  C A ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseAB C A B H1); try immediate9
	| context [(MidPoint C A ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseAB C A B H1); try immediate9

	| context [(MidLine A C ?H1)] => apply (EquiOrientedMidLineClockwiseBA A C B H1); try immediate9
	| context [(MidPoint A C ?H1)] => apply (EquiOrientedMidLineClockwiseBA A C B H1); try immediate9
	| context [(MidLine C B ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseBA C B A H1); try immediate9
	| context [(MidPoint C B ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseBA C B A H1); try immediate9
	| context [(MidLine B A ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseBA B A C H1); try immediate9
	| context [(MidPoint B A ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseBA B A C H1); try immediate9
end.

Ltac stepOnLine9 := match goal with
	| |- OnLine (MidLine _ _ _) _ => apply EqDistanceOnMidLine; try solveDist9
	| |- OnLine (Ruler _ _ _) _ => simplGoal0; try immCollinear9
end.

Ltac step9 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance9 H
	| |- _ = DistancePlus _ _  => stepEqDistance9 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance9 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance9 H
	| |- Distance _ _ = _ => stepEqDistance9 H
	| |- _ = Distance _ _ => stepEqDistance9 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |-  Supplement ?A ?B ?C ?D ?E ?F => stepSupplement8 A B C D E F H
	| |-  OpposedAngles ?A ?B ?C ?D ?E => stepOpposed8 A B C D E H

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent8; try immediate8
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent8; try immediate8

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle8 A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle8 A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle8 A B C H

	| |- _ = H => try unfold H; byDefEqPoint9
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint9

	| |- ?A = ?B => stepEq8 A B H
	| |- ?A <> ?B => stepDistinct3 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct3 A B H

	| |- Collinear _ _ _  => stepCollinear6 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented1 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay6 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay6 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise9 A B C H
	| |- Between ?A ?B ?D => stepBetween8 A B D H
	| |- Segment ?A ?B ?C  => stepSegment8 A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec2 A B C D E F H

	| |- OnLine H _ => unfold H; stepOnLine9
	| |- Diameter H ?c => unfold Diameter, H; simpl Center; stepOnLine9

	| |- TStrict ?t => stepTStrict7 t H

	| |- TCongruent _ _ => stepTCongruent7 H

end.

Ltac since9 txt := assert txt; try immediate9.

Ltac from9 H txt := assert txt; [(step9 H ; try immediate9) |  try immediate9].

Ltac as9 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate9 | (step9 Hyp ; try immediate9)]).

Ltac setMidLine9 A B m := match goal with
| H : A <> B |- _ => pose (m := MidLine A B H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B H);
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B H);
			fold m in Hyp1, Hyp2))
| H : A = B -> False |- _ => pose (m := MidLine A B H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B H);
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B H);
			fold m in Hyp1, Hyp2))
| H : B = A -> False |- _ => pose (m := MidLine A B (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B (sym_not_eq H));
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B (sym_not_eq H));
			fold m in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : A <> B);
	[try immediate8 | pose (m := MidLine A B H); 
		let Hyp1 := fresh in (
			assert (Hyp1 := OnMidLineEqDistance A B H);
			let Hyp2 := fresh in (
				assert (Hyp2 := EqDistanceOnMidLine A B H);
				fold m in Hyp1, Hyp2))])
end.
	
Ltac setMidPoint9 A B C :=
match goal with
| H : A <> B |- _ => pose (C := MidPoint A B H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := MidPointBetween A B H);
		let Hyp2 := fresh in (
			assert (Hyp2 := MidPointEqDistance A B H);
			fold C in Hyp1, Hyp2))
| H : A = B -> False |- _ => pose (C := MidPoint A B H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := MidPointBetween A B H);
		let Hyp2 := fresh in (
			assert (Hyp2 := MidPointEqDistance A B H);
			fold C in Hyp1, Hyp2))
| H : B <> A |- _ => pose (C := MidPoint A B (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := MidPointBetween A B (sym_not_eq H));
		let Hyp2 := fresh in (
			assert (Hyp2 := MidPointEqDistance A B (sym_not_eq H));
			fold C in Hyp1, Hyp2))
| H : B = A -> False |- _ => pose (C := MidPoint A B (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := MidPointBetween A B (sym_not_eq H));
		let Hyp2 := fresh in (
			assert (Hyp2 := MidPointEqDistance A B (sym_not_eq H));
			fold C in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : A <> B);
	[try immediate8 | pose (C := MidPoint A B H);
		let Hyp1 := fresh in (
			assert (Hyp1 := MidPointBetween A B H);
			let Hyp2 := fresh in (
				assert (Hyp2 := MidPointEqDistance A B H);
				fold C in Hyp1, Hyp2))])
end.


