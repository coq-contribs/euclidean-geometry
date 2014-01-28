Require Import A1_Plan A2_Orientation A4_Droite A5_Cercle A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics .
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F4_ArchimedianDistance F5_Tactics .
Require Import G1_Angles G2_AngleProp G3_ParticularAngle G4_Tactics .
Require Import H1_Triangles H2_ParticularTriangles H4_Tactics .
Require Import I1_SupplementaryAngle I2_Supplement I3_OpposedAngles I4_Tactics .
Require Import J1_MidLine J2_MidPoint J3_MidProp J4_Tactics .
Require Import K1_RightAngle K2_MidLineandRightAngle.


Ltac congruentToEq10 := unfold NullAngle, ElongatedAngle, RightAngle in *;
repeat match goal with
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- _ => match goal with
		| Hba : B <> A, Hbc : B <> C, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| _ => inversion_clear H
		end

	| H : Supplement ?A ?B ?C ?D ?E ?F |- _ => match goal with
		| Hba : B <> A, Hbc : B <> C, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (SupplementSupplementary A B C D E F Hba Hbc Hed Hef H)); clear H
		| _ => inversion_clear H
		end

	| H : OpposedAngles ?A ?B ?C ?D ?E  |- _ => let Hyp := fresh in assert (Hyp := (OpposedCongruentAngles A B C D E H)); clear H
end; 
match goal with
	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => 
		match goal with
			| Hba : B <> A |- _  => congruentToEqAngleHba6 A B C D E F Hba
			| _ =>  let Hba := fresh in (assert (Hba : B <> A); [try immediate5 | congruentToEqAngleHba6 A B C D E F Hba])
		end

	| |- Supplement ?A ?B ?C ?D ?E ?F => 
		match goal with
			| Hba : B <> A |- _  => supplementAngleHba8 A B C D E F Hba
			| _ =>  let Hba := fresh in (assert (Hba : B <> A); [try immediate5 | supplementAngleHba8 A B C D E F Hba])
		end 

	| _ => idtac
end.

Ltac eqToCongruent10 := repeat match goal with
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Angle ?D ?E ?F ?Hed ?Hef  |- _ => let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C D E F Hba Hbc Hed Hef H)); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef)  |- _ => let Hyp := fresh in assert (Hyp := (EqAngleSupplement A B C D E F Hba Hbc Hed Hef H)); clear H
	| H : Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef) = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (EqAngleSupplement A B C D E F Hba Hbc Hed Hef (sym_eq H))); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = Uu  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc H)); clear H
	| H : Uu = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc (sym_eq H))); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = uU  |- _ => let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc H)); clear H
	| H : uU = Angle ?A ?B ?C ?Hba ?Hbc  |- _ =>  let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc (sym_eq H))); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = Vv  |- _ => let Hyp := fresh in assert (Hyp := (AngleVvEqRight A B C Hba Hbc H)); clear H
	| H : Vv = Angle ?A ?B ?C ?Hba ?Hbc  |- _ =>  let Hyp := fresh in assert (Hyp := (AngleVvEqRight A B C Hba Hbc (sym_eq H))); clear H

	| Ha : IsAngle ?alpha, H : Angle ?A ?B ?C ?Hba ?Hbc = ?alpha |- _ => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha Ha) Ha) in H;  let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C Uu Oo alpha Hba Hbc DistinctOoUu (IsAngleDistinctOo alpha Ha) H)); clear H
	| Ha : IsAngle ?alpha, H : ?alpha = Angle ?A ?B ?C ?Hba ?Hbc |- _ => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha Ha) Ha) in H; let Hyp := fresh in assert (Hyp := (CongruentEqAngle Uu Oo alpha A B C DistinctOoUu (IsAngleDistinctOo alpha Ha) Hba Hbc H)); clear H

end; match goal with
	| |- Angle ?A ?B ?C ?Hba ?Hbc = Angle ?D ?E ?F ?Hed ?Hef => apply (EqCongruentAngle A B C D E F Hba Hbc Hed Hef)

	| |- Angle ?A ?B ?C ?Hba ?Hbc = Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef)  => apply (SupplementSupplementary A B C D E F Hba Hbc Hed Hef)
	| |- Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef) = Angle ?A ?B ?C ?Hba ?Hbc => apply sym_eq; apply (SupplementSupplementary A B C D E F Hba Hbc Hed Hef)

	| |- Angle ?A ?B ?C ?Hba ?Hbc = Uu => apply (EqNullAngle A B C Hba Hbc)
	| |- Uu = Angle ?A ?B ?C ?Hba ?Hbc => apply sym_eq; apply (EqNullAngle A B C Hba Hbc)

	| |- Angle ?A ?B ?C ?Hba ?Hbc = uU => apply (EqElongatedAngle A B C Hba Hbc)
	| |- uU = Angle ?A ?B ?C ?Hba ?Hbc => apply sym_eq; apply (EqElongatedAngle A B C Hba Hbc)

	| |- Angle ?A ?B ?C ?Hba ?Hbc = Vv => apply (RightEqAngleVv A B C Hba Hbc)
	| |- Vv = Angle ?A ?B ?C ?Hba ?Hbc => apply sym_eq; apply (RightEqAngleVv A B C Hba Hbc)

	| H : IsAngle ?alpha  |- Angle ?A ?B ?C ?Hba ?Hbc = ?alpha => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H); apply EqCongruentAngle
	| H : IsAngle ?alpha |- ?alpha = Angle ?A ?B ?C ?Hba ?Hbc => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H); apply EqCongruentAngle

	| _ => idtac
end.

Ltac simplDistance10 := intros; splitIsAngle6; simplCircle2; repeat 
(match goal with 
	| H : context [(Distance ?X ?X)] |- _ => rewrite (NullDistance X) in H
	| |- context [(Distance ?X ?X)] => rewrite (NullDistance X) 

	| H : context [(Distance Oo Uu)] |- _ => rewrite UnitDistance in H
	| |- context [(Distance Oo Uu)] => rewrite UnitDistance 
	| H : context [(Distance Uu Oo)] |- _ => rewrite (DistanceSym Uu Oo) in H; rewrite UnitDistance in H
	| |- context [(Distance Uu Oo)] => rewrite (DistanceSym Uu Oo); rewrite UnitDistance 

	| H : context [(Distance Oo uU)] |- _ => rewrite DistanceOouU in H
	| |- context [(Distance Oo uU)] => rewrite DistanceOouU 
	| H : context [(Distance uU Oo)] |- _ => rewrite (DistanceSym uU Oo) in H; rewrite DistanceOouU in H
	| |- context [(Distance uU Oo)] => rewrite (DistanceSym uU Oo); rewrite DistanceOouU 

	| H : context [(Distance Oo Vv)] |- _ => rewrite DistanceOoVv in H
	| |- context [(Distance Oo Vv)] => rewrite DistanceOoVv 
	| H : context [(Distance Vv Oo)] |- _ => rewrite (DistanceSym Vv Oo) in H; rewrite DistanceOoVv in H
	| |- context [(Distance Vv Oo)] => rewrite (DistanceSym Vv Oo); rewrite DistanceOoVv 

	| H : context [(Distance Vv uU)] |- _ => rewrite <- EqDistanceVvUuuU in H
	| |- context [(Distance Vv uU)] => rewrite <- EqDistanceVvUuuU 
	| H : context [(Distance uU Vv)] |- _ => rewrite (DistanceSym uU Vv) in H; rewrite <- EqDistanceVvUuuU in H
	| |- context [(Distance uU Vv)] => rewrite (DistanceSym uU Vv); rewrite <- EqDistanceVvUuuU 

	| H : context [(Distance (Supplementary ?alpha ?Ha) Uu)] |- _ => rewrite (DistanceSym (Supplementary alpha Ha) Uu) in H; rewrite <- (EqDistanceUuSupplementary alpha Ha) in H
	| |- context [(Distance (Supplementary ?alpha ?Ha) Uu)] => rewrite (DistanceSym (Supplementary alpha Ha) Uu); rewrite <- (EqDistanceUuSupplementary alpha Ha)
	| H : context [(Distance Uu (Supplementary ?alpha ?Ha))] |- _ => rewrite <- (EqDistanceUuSupplementary alpha Ha) in H
	| |- context [(Distance Uu (Supplementary ?alpha ?Ha))] => rewrite <- (EqDistanceUuSupplementary alpha Ha) 

	| H1 : IsDistance ?d,  H2 : context [(Distance Oo ?d)] |- _ => rewrite (IsDistanceEqDistance d H1) in H2
	| H1 : IsDistance ?d |- context [(Distance Oo ?d)] => rewrite (IsDistanceEqDistance d H1) 
	| H1 : IsDistance ?d,  H2 : context [(Distance ?d Oo)] |- _ => rewrite (DistanceSym d Oo) in H2; rewrite (IsDistanceEqDistance d H1) in H2
	| H1 : IsDistance ?d |- context [(Distance ?d Oo)] => rewrite (DistanceSym d Oo); rewrite (IsDistanceEqDistance d H1) 

	| H : context [(Distance Oo (Distance ?X ?Y))] |- _ => rewrite (EqDistanceDistance X Y) in H
	| |- context [(Distance Oo (Distance ?X ?Y))] => rewrite (EqDistanceDistance X Y)  
	| H : context [(Distance (Distance ?X ?Y) Oo)] |- _ => rewrite (DistanceSym (Distance X Y) Oo) in H; rewrite (EqDistanceDistance X Y) in H
	| |- context [(Distance (Distance ?X ?Y) Oo)] => rewrite (DistanceSym (Distance X Y) Oo); rewrite (EqDistanceDistance X Y)  

	| H : context [(Distance Oo (DistancePlus ?X ?Y))] |- _ => rewrite (EqDistanceDistancePlus X Y) in H
	| |- context [(Distance Oo (DistancePlus ?X ?Y))] => rewrite (EqDistanceDistancePlus X Y)  
	| H : context [(Distance (DistancePlus ?X ?Y) Oo)] |- _ => rewrite (DistanceSym (Distance X Y) Oo) in H; rewrite (EqDistanceDistancePlus X Y) in H
	| |- context [(Distance (DistancePlus ?X ?Y) Oo)] => rewrite (DistanceSym (Distance X Y) Oo); rewrite (EqDistanceDistancePlus X Y)  

	| H : context [(DistancePlus ?X  Oo)] |- _ => rewrite (DistancePlusNeutralRight X) in H
	| |- context [(DistancePlus ?X Oo)] => rewrite (DistancePlusNeutralRight X)  
	| H : context [(DistancePlus Oo ?X)] |- _ => rewrite (DistancePlusNeutralLeft X) in H
	| |- context [(DistancePlus Oo ?X)] => rewrite (DistancePlusNeutralLeft X)  

	| H : context [(DistancePlus ?X  (Distance Oo ?Y))] |- _ => rewrite <- (DistancePlusOoN X Y) in H
	| |- context [(DistancePlus ?X  (Distance Oo ?Y))] => rewrite <- (DistancePlusOoN X Y) 
	| H : context [(DistancePlus ?X  (Distance ?Y Oo))] |- _ => rewrite (DistanceSym Y Oo);  rewrite <- (DistancePlusOoN X Y) in H
	| |- context [(DistancePlus ?X  (Distance ?Y Oo))] => rewrite (DistanceSym Y Oo);  rewrite <- (DistancePlusOoN X Y) 

	| H : context [(DistanceTimes _ _ _)] |- _ => progress simpl DistanceTimes in H
	| |- context [(DistanceTimes _ _ _)] => progress simpl DistanceTimes   

	| H : context [(Distance (Center ?c) (InterDiameterPoint ?l ?c ?Hd))] |- _ => rewrite (EqDistanceInterDiameterPoint l c Hd)  in H
	| |- context [(Distance (Center ?c) (InterDiameterPoint ?l ?c ?Hd))] => rewrite (EqDistanceInterDiameterPoint l c Hd)  
	| H : context [(Distance (InterDiameterPoint ?l ?c ?Hd) (Center ?c))] |- _ => rewrite (DistanceSym (InterDiameterPoint l c Hd) (Center c)) in H; rewrite (EqDistanceInterDiameterPoint l c Hd)  in H
	| |- context [(Distance (InterDiameterPoint ?l ?c ?Hd) (Center ?c))] => rewrite (DistanceSym (InterDiameterPoint l c Hd) (Center c)); rewrite (EqDistanceInterDiameterPoint l c Hd)

	| H : context [(Distance (Center ?c) (SecondInterDiameterPoint ?l ?c ?Hd))] |- _ => rewrite (EqDistanceSecondInterDiameterPoint l c Hd)  in H
	| |- context [(Distance (Center ?c) (SecondInterDiameterPoint ?l ?c ?Hd))] => rewrite (EqDistanceSecondInterDiameterPoint l c Hd)  
	| H : context [(Distance (SecondInterDiameterPoint ?l ?c ?Hd) (Center ?c))] |- _ => rewrite (DistanceSym (SecondInterDiameterPoint l c Hd) (Center c)) in H; rewrite (EqDistanceSecondInterDiameterPoint l c Hd)  in H
	| |- context [(Distance (SecondInterDiameterPoint ?l ?c ?Hd) (Center ?c))] => rewrite (DistanceSym (SecondInterDiameterPoint l c Hd) (Center c)); rewrite (EqDistanceSecondInterDiameterPoint l c Hd)

	| H : context [(Distance ?C (AddSegmentPoint ?A ?B ?C ?D ?E ?H0 ?H1))] |- _ => rewrite (EqDistanceAddSegmentPoint A B C D E H0 H1)  in H
	| |- context [(Distance ?C (AddSegmentPoint ?A ?B ?C ?D ?E ?H0 ?H1))] => rewrite (EqDistanceAddSegmentPoint A B C D E H0 H1)  
	| H : context [(Distance (AddSegmentPoint ?A ?B ?C ?D ?E ?H0 ?H1) ?C)] |- _ => rewrite (DistanceSym (AddSegmentPoint A B C D E H0 H1) C) in H; rewrite (EqDistanceAddSegmentPoint A B C D E H0 H1)  in H
	| |- context [(Distance (AddSegmentPoint ?A ?B ?C ?D ?E ?H0 ?H1) ?C)] => rewrite (DistanceSym (AddSegmentPoint A B C D E H0 H1) C); rewrite (EqDistanceAddSegmentPoint A B C D E H0 H1)

	| H : context [(Distance ?A (MarkSegmentPoint ?A ?B ?C ?D ?H0 ))] |- _ => rewrite (EqDistanceMarkSegmentPoint A B C D H0)  in H
	| |- context [(Distance ?A (MarkSegmentPoint ?A ?B ?C ?D ?H0))] => rewrite (EqDistanceMarkSegmentPoint A B C D H0)  
	| H : context [(Distance (MarkSegmentPoint ?A ?B ?C ?D ?H0) ?A)] |- _ => rewrite (DistanceSym (MarkSegmentPoint A B C D H0) A) in H; rewrite (EqDistanceMarkSegmentPoint A B C D H0)  in H
	| |- context [(Distance (MarkSegmentPoint ?A ?B ?C ?D ?H0) ?A)] => rewrite (DistanceSym (MarkSegmentPoint A B C D H0) A); rewrite (EqDistanceMarkSegmentPoint A B C D H0)

	| H : context [(Distance ?A (OppSegmentPoint ?A ?B ?C ?D ?H0 ))] |- _ => rewrite (EqDistanceOppSegmentPoint A B C D H0)  in H
	| |- context [(Distance ?A (OppSegmentPoint ?A ?B ?C ?D ?H0))] => rewrite (EqDistanceOppSegmentPoint A B C D H0)  
	| H : context [(Distance (OppSegmentPoint ?A ?B ?C ?D ?H0) ?A)] |- _ => rewrite (DistanceSym (OppSegmentPoint A B C D H0) A) in H; rewrite (EqDistanceOppSegmentPoint A B C D H0)  in H
	| |- context [(Distance (OppSegmentPoint ?A ?B ?C ?D ?H0) ?A)] => rewrite (DistanceSym (OppSegmentPoint A B C D H0) A); rewrite (EqDistanceOppSegmentPoint A B C D H0)

	| H : context [(Distance ?B (SymmetricPoint ?A ?B ?H0 ))] |- _ => rewrite (EqDistanceSymmetricPoint A B H0)  in H
	| |- context [(Distance ?B (SymmetricPoint ?A ?B ?H0))] => rewrite (EqDistanceSymmetricPoint A B H0)  
	| H : context [(Distance (SymmetricPoint ?A ?B ?H0) ?B)] |- _ => rewrite (DistanceSym (SymmetricPoint A B H0) B) in H; rewrite (EqDistanceSymmetricPoint A B H0)  in H
	| |- context [(Distance (SymmetricPoint ?A ?B ?H0) ?B)] => rewrite (DistanceSym (SymmetricPoint A B H0) B); rewrite (EqDistanceSymmetricPoint A B H0)

	| H : context [(Distance (Graduation ?n ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab))] |- _ => rewrite (EqDistanceGraduation n A B Hab)  in H
	| |- context [(Distance (Graduation ?n ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab))] => rewrite (EqDistanceGraduation n A B Hab)  
	| H : context [(Distance (Graduation (S ?n) ?A ?B ?Hab) (Graduation ?n ?A ?B ?Hab))] |- _ => rewrite (DistanceSym (Graduation (S n) A B Hab) (Graduation n A B Hab)) in H; rewrite (EqDistanceGraduation n A B Hab)  in H
	| |- context [(Distance (Graduation (S ?n) ?A ?B ?Hab) (Graduation ?n ?A ?B ?Hab))] => rewrite (DistanceSym (Graduation (S n) A B Hab) (Graduation n A B Hab)); rewrite (EqDistanceGraduation n A B Hab)

	| H : context [(Distance ?A (Graduation ?n ?A ?B ?Hab))] |- _ => rewrite (DistanceGraduation n A B Hab)  in H
	| |- context [(Distance ?A (Graduation ?n ?A ?B ?Hab))] => rewrite (DistanceGraduation n A B Hab)  
	| H : context [(Distance (Graduation ?n ?A ?B ?Hab) ?A)] |- _ => rewrite (DistanceSym (Graduation n A B Hab) A) in H; rewrite (DistanceGraduation n A B Hab)  in H
	| |- context [(Distance (Graduation ?n ?A ?B ?Hab) ?A)] => rewrite (DistanceSym (Graduation n A B Hab) A); rewrite (DistanceGraduation n A B Hab)
end).

Ltac solveDistance10 := simplDistance10; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus9
	| |- _ = DistancePlus _ _ => solveDistPlus9

	| |- DistanceTimes _ _ _ = _ => solveDistTimes9
	| |- _ = DistanceTimes _ _ _ => solveDistTimes9

	| |- Distance _ _ = _ => solveDist9
	| |- _ = Distance _ _ => apply sym_eq; solveDist9

	| |- _ => solveEq9
end.

Ltac immOnLine10 := match goal with
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

	| |- OnLine (Ruler _ _ _) _ => simpl; immediate8
	| |- OnLine ?d _ => unfold d; simpl; immediate8
end.

Ltac immNotCollinear10 := match goal with
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?A ?B ?C => exact H	
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?A ?C ?B => intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?B ?A ?C =>  intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?B ?C ?A =>  intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?C ?A ?B =>  intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?C ?B ?A =>  intro; elim H; immCollinear1

	| H : RightAngle ?A ?B ?C |- ~Collinear ?A ?B ?C => apply (RightAngleNotCollinear A B C H)
	| H : RightAngle ?A ?B ?C |- ~Collinear ?A ?C ?B => assert (RightAngleNotCollinear A B C H); immNotCollinear1
	| H : RightAngle ?A ?B ?C |- ~Collinear ?B ?A ?C =>  assert (RightAngleNotCollinear A B C H); immNotCollinear1
	| H : RightAngle ?A ?B ?C |- ~Collinear ?B ?C ?A =>  assert (RightAngleNotCollinear A B C H); immNotCollinear1
	| H : RightAngle ?A ?B ?C |- ~Collinear ?C ?A ?B =>  assert (RightAngleNotCollinear A B C H); immNotCollinear1
	| H : RightAngle ?A ?B ?C |- ~Collinear ?C ?B ?A =>  assert (RightAngleNotCollinear A B C H); immNotCollinear1

	|  |- ~Collinear ?A ?B ?C => apply ClockwiseABCNotCollinear; immClockwise1
	|  |- ~Collinear ?A ?B ?C => apply ClockwiseBACNotCollinear; immClockwise1
end.

Ltac immClockwise10 := match goal with
	| |- Clockwise uU Vv Uu => apply ClockwiseuUVvUu
	| |- Clockwise Vv Uu uU => apply ClockwiseBCA; apply ClockwiseuUVvUu
	| |- Clockwise Uu uU Vv => apply ClockwiseCAB; apply ClockwiseuUVvUu

	| |- Clockwise Oo Vv Uu => apply ClockwiseOoVvUu
	| |- Clockwise Vv Uu Oo => apply ClockwiseBCA; apply ClockwiseOoVvUu
	| |- Clockwise Uu Oo Vv => apply ClockwiseCAB; apply ClockwiseOoVvUu

	| H : Clockwise ?A ?B ?C |- Clockwise ?A ?B ?C => exact H	
	| H : Clockwise ?A ?B ?C |- Clockwise ?B ?C ?A => exact (ClockwiseBCA A B C H)
	| H : Clockwise ?A ?B ?C |- Clockwise ?C ?A ?B => exact (ClockwiseCAB A B C H)

	| |- Clockwise  ?A (LineA (MidLine ?A ?B _)) ?B => apply ClockwiseAMidLineAB
	| |- Clockwise  (LineA (MidLine ?A ?B _)) ?B ?A => apply ClockwiseBCA; apply ClockwiseAMidLineAB
	| |- Clockwise ?B  ?A (LineA (MidLine ?A ?B _)) => apply ClockwiseCAB; apply ClockwiseAMidLineAB

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

Ltac immNotClockwise10 := match goal with
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
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?B ?C ?A => intro; elim H; immClockwise10
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?C ?A ?B => intro; elim H; immClockwise10

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?D => apply (EquiOrientedNotClockwiseABD _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?D ?A => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise10
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?D ?A ?B => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise10

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?C => apply (EquiOrientedNotClockwiseABC _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?C ?A => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise10
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?C ?A ?B => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise10

	|  |- ~Clockwise ?A ?B ?C => apply ClockwiseNotClockwise; immClockwise10
	|  |- ~Clockwise ?A ?B ?C => apply CollinearNotClockwise; immCollinear9 
end.

Ltac immDistinct10 := match goal with
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

	| |- Oo <> Vv => exact DistinctOoVv
	| |- Vv <> Oo => apply sym_not_eq; exact DistinctOoVv

	| |- Uu <> Vv => exact DistinctUuVv
	| |- Vv <> Uu => apply sym_not_eq; exact DistinctUuVv

	| |- uU <> Vv => exact DistinctuUVv
	| |- Vv <> uU => apply sym_not_eq; exact DistinctuUVv

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

	| H : RightAngle ?A ?B ?C |- ?B <> ?A => apply (RightAngleDistinctBA _ _ _ H)
	| H : RightAngle ?A ?B ?C |- ?A <> ?B => apply sym_not_eq; apply (RightAngleDistinctBA _ _ _ H)
	| H : RightAngle ?A ?B ?C |- ?B <> ?C => apply (RightAngleDistinctBC _ _ _ H)
	| H : RightAngle ?A ?B ?C |- ?C <> ?B => apply sym_not_eq; apply (RightAngleDistinctBC _ _ _ H)

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

Ltac immIsAngle10 := match goal with
	| H : IsAngle ?alpha |- IsAngle ?alpha => exact H

	| |- IsAngle Uu => apply IsAngleNullAngle
	| |- IsAngle uU => apply IsAngleElongatedAngle
	| |- IsAngle Vv => apply IsAngleVv

	| |- IsAngle (Angle _ _ _ _ _) =>  apply IsAngleAngle
	| |- IsAngle (Supplementary _ _ ) =>  apply IsAngleSupplementary

	| |- IsAngle _ => unfold IsAngle; simplCircle2; split; immediate5
end.

Ltac immRightAngle10   := match goal with
	| |- RightAngle Uu Oo Vv => exact RightUuOoVv
	| |- RightAngle Vv Oo Uu => apply RightAngleSym; exact RightUuOoVv
	| |- RightAngle Vv Oo uU => exact RightVvOouU
	| |- RightAngle uU Oo Vv => apply RightAngleSym; exact RightVvOouU

	| H : RightAngle ?A ?B ?C |- RightAngle ?A ?B ?C => exact H
	| H : RightAngle ?A ?B ?C |- RightAngle ?C ?B ?A => apply RightAngleSym; exact H

	| H : Supplement ?A ?B ?C ?A ?B ?C |- RightAngle ?A ?B ?C => apply EqSupplementEqRightAngle; exact H
	| H : Supplement ?A ?B ?C ?A ?B ?C |- RightAngle ?C ?B ?A => apply RightAngleSym; apply EqSupplementEqRightAngle; exact H
	| H : Supplement ?C ?B ?A ?A ?B ?C |- RightAngle ?A ?B ?C => apply EqSupplementEqRightAngle; apply SupplementRev1; exact H
	| H : Supplement ?C ?B ?A ?A ?B ?C |- RightAngle ?C ?B ?A => apply EqSupplementEqRightAngle; apply SupplementRev2; exact H

	| |- RightAngle ?A (MidPoint ?A ?B ?H) (LineA (MidLine ?A ?B ?H)) => apply RightAngleAIA'
	| |- RightAngle (LineA (MidLine ?A ?B ?H)) (MidPoint ?A ?B ?H) ?A => apply RightAngleSym; apply RightAngleAIA'
	| |- RightAngle ?A (MidPoint ?A ?B ?H) (LineB (MidLine ?A ?B ?H)) => apply RightAngleAIB'
	| |- RightAngle (LineB (MidLine ?A ?B ?H)) (MidPoint ?A ?B ?H) ?A => apply RightAngleSym; apply RightAngleAIB'
	| |- RightAngle ?B (MidPoint ?A ?B ?H) (LineA (MidLine ?A ?B ?H)) => apply RightAngleBIA'
	| |- RightAngle (LineA (MidLine ?A ?B ?H)) (MidPoint ?A ?B ?H) ?B => apply RightAngleSym; apply RightAngleBIA'
	| |- RightAngle ?B (MidPoint ?A ?B ?H) (LineB (MidLine ?A ?B ?H)) => apply RightAngleBIB'
	| |- RightAngle (LineB (MidLine ?A ?B ?H)) (MidPoint ?A ?B ?H) ?B => apply RightAngleSym; apply RightAngleBIB'

end.

Ltac immNotNullAngle10 := match goal with 
	| H : ElongatedAngle ?A ?B ?C |- ~NullAngle ?A ?B ?C => apply (ElongatedAngleNotNullAngle A B C H)
	| H : ElongatedAngle ?A ?B ?C |- ~NullAngle ?C ?B ?A => apply (ElongatedAngleNotNullAngle C B A); immElongatedAngle6
	| H : RightAngle ?A ?B ?C |- ~NullAngle ?A ?B ?C => apply (RightAngleNotNullAngle A B C H)
	| H : RightAngle ?A ?B ?C |- ~NullAngle ?C ?B ?A => apply (RightAngleNotNullAngle C B A); immRightAngle10
end.

Ltac immNotElongatedAngle10 := match goal with 
	| H : NullAngle ?A ?B ?C |- ~ElongatedAngle ?A ?B ?C => apply (NullAngleNotElongatedAngle A B C H)
	| H : NullAngle ?A ?B ?C |- ~ElongatedAngle ?C ?B ?A => apply (NullAngleNotElongatedAngle C B A); immNullAngle6
	| H : RightAngle ?A ?B ?C |- ~ElongatedAngle ?A ?B ?C => apply (RightAngleNotElongatedAngle A B C H)
	| H : RightAngle ?A ?B ?C |- ~ElongatedAngle ?C ?B ?A => apply (RightAngleNotElongatedAngle C B A); immRightAngle10
end.

Ltac immNotRightAngle10 := match goal with 
	| H : NullAngle ?A ?B ?C |- ~RightAngle ?A ?B ?C => apply (NullAngleNotRightAngle A B C H)
	| H : NullAngle ?A ?B ?C |- ~RightAngle ?C ?B ?A => apply (NullAngleNotRightAngle C B A); immNullAngle6
	| H : ElongatedAngle ?A ?B ?C |- ~RightAngle ?A ?B ?C => apply (ElongatedAngleNotRightAngle A B C H)
	| H : ElongatedAngle ?A ?B ?C |- ~RightAngle ?C ?B ?A => apply (ElongatedAngleNotRightAngle C B A); immElongatedAngle6
end.

Ltac immSupplement10 := match goal with
	|  |- Supplement Uu Oo Uu Uu Oo uU => exact SupplementUuuU
	|  |- Supplement Uu Oo Uu uU Oo Uu =>  apply SupplementRev2; exact SupplementUuuU
	|  |- Supplement Uu Oo uU Uu Oo Uu => apply SupplementSym; exact SupplementUuuU
	|  |- Supplement uU Oo Uu Uu Oo Uu =>  apply SupplementSym; apply SupplementRev2; exact SupplementUuuU
 
	|  |- Supplement Uu Oo Vv Uu Oo Vv => exact RightSupplementUuOoVv
	|  |- Supplement Uu Oo Vv Vv Oo Uu =>  apply SupplementRev2; exact RightSupplementUuOoVv
	|  |- Supplement Vv Oo Uu Uu Oo Vv => apply SupplementRev1; exact RightSupplementUuOoVv
	|  |- Supplement Vv Oo Uu Vv Oo Uu =>  apply SupplementRev1; apply SupplementRev2; exact RightSupplementUuOoVv
 
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?A ?B ?C ?D ?E ?F => exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?C ?B ?A ?D ?E ?F =>  apply SupplementRev1; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?A ?B ?C ?F ?E ?D => apply SupplementRev2; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?C ?B ?A ?F ?E ?D =>  apply SupplementRev1; apply SupplementRev2; exact H
 
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?D ?E ?F ?A ?B ?C=>  apply SupplementSym; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?D ?E ?F ?C ?B ?A=>   apply SupplementSym; apply SupplementRev1; exact H 
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?F ?E ?D ?A ?B ?C=>  apply SupplementSym; apply SupplementRev2; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?F ?E ?D ?C ?B ?A=>   apply SupplementSym; apply SupplementRev1; apply SupplementRev2; exact H
 
	| H : RightAngle ?A ?B ?C |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle10
	| H : RightAngle ?C ?B ?A |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle10
	| H : RightAngle ?D ?E ?F |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle10
	| H : RightAngle ?F ?E ?D |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle10

	| H : Between ?B ?A ?D |- Supplement ?B ?A ?C ?C ?A ?D => apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?B ?C ?A ?D => apply SupplementRev1; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?B ?A ?C ?D ?A ?C => apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?B ?D ?A ?C => apply SupplementRev1; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]

	| H : Between ?B ?A ?D |- Supplement ?C ?A ?D ?B ?A ?C => apply SupplementSym; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?D ?C ?A ?B => apply SupplementSym; apply SupplementRev1; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?D ?A ?C ?B ?A ?C => apply SupplementSym; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?D ?A ?C ?C ?A ?B => apply SupplementSym; apply SupplementRev1; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
end.

Ltac immCongruentAngle10 := match goal with 
	| |- CongruentAngle ?A ?B ?C ?A ?B ?C => apply (CongruentAngleRefl A B C); try  immDistinct6
	| |- CongruentAngle ?A ?B ?C ?C ?B ?A => apply (CongruentAnglePerm A B C); try  immDistinct6

	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- _ => orderAngle7 A B C D E F; exact H 

	|H : Angle ?A ?B ?C ?H1 ?H2  = Angle ?D ?E ?F ?H3 ?H4  |- _ => orderAngle7 A B C D E F; apply (CongruentEqAngle A B C D E F H1 H2 H3 H4 H)

	| H : RightAngle ?A ?B ?C  |- _ => orderAngle7 A B C Uu Oo Vv; exact H 
	| H : RightAngle ?A ?B ?C  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle10 
	| H : RightAngle ?C ?B ?A  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle10 
	| H : RightAngle ?D ?E ?F  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle10 
	| H : RightAngle ?F ?E ?D  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle10 

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

	| H : OpposedAngles ?A ?B ?C ?D ?E |- CongruentAngle _ ?A _ _ ?A _ => orderAngle7  B A C D A E; apply OpposedCongruentAngles; immediate6
end.

Ltac solveAngle10 := match goal with 
	| |- Angle _ _ _ _ _ = Angle _ _ _ _ _ => apply EqCongruentAngle; immCongruentAngle10

	| |- Angle _ _ _ _ _ = Supplementary  _ _ => apply SupplementSupplementary; immSupplement10
	| |- Supplementary  _ _ = Angle _ _ _ _ _  => apply sym_eq; apply SupplementSupplementary; immSupplement10

	| |- Angle ?A ?B ?C _ _ = Uu => eqToCongruent10; immNullAngle6
	| |- Uu = Angle ?A ?B ?C _ _ => eqToCongruent10; immNullAngle6

	| |- Angle ?A ?B ?C _ _ = uU => eqToCongruent10; immElongatedAngle6
	| |- uU = Angle ?A ?B ?C _ _ => eqToCongruent10; immElongatedAngle6

	| |- Angle ?A ?B ?C _ _ = Vv => eqToCongruent10; immRightAngle10
	| |- Vv = Angle ?A ?B ?C _ _ => eqToCongruent10; immRightAngle10

	| |- Angle Uu Oo ?M _ _ = ?M => apply EqAnglePoint; immIsAngle10
	| |- ?M = Angle Uu Oo ?M _ _  => apply sym_eq; apply EqAnglePoint; immIsAngle10
	| |- Angle ?M Oo Uu ?H1 ?H2 = ?M => rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2));  apply EqAnglePoint; immIsAngle10
	| |- ?M = Angle ?M Oo Uu ?H1 ?H2  => apply sym_eq;  rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2)); apply EqAnglePoint; immIsAngle10

end.

Ltac solveSupplementary10 :=  match goal with
	| |- Supplementary _ _ = Supplementary _ _ => apply SupplementaryEqAngles; solveSupplementary10
	| |- Supplementary (Supplementary _ _) _ = _ => rewrite SupplementarySupplementary; solveSupplementary10
	| |- _ = Supplementary (Supplementary _ _) _ => rewrite SupplementarySupplementary; solveSupplementary10

	| |- Supplementary Uu _ = _ => rewrite SupplementaryNullAngle; solveSupplementary10	| |- _ = Supplementary Uu _  => rewrite SupplementaryNullAngle; solveSupplementary10	| |- Supplementary uU _ = _ => rewrite SupplementaryElongatedAngle; solveSupplementary10	| |- _ = Supplementary uU _  => rewrite SupplementaryElongatedAngle; solveSupplementary10

	| |- Supplementary Vv _ = _ => rewrite SupplementaryRightAngle; solveAngle10
	| |- _ = Supplementary Vv _  => rewrite SupplementaryRightAngle; solveAngle10	

	| |- _ = _ => solveAngle10
end.

Ltac immediate10 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate10
	| |- ?A \/ ?B => (left; immediate10)  || (right; immediate10)

	| |- DistancePlus _ _ = _ => solveDistance10
	| |- _ = DistancePlus _ _ => solveDistance10

	| |- DistanceTimes _ _ _ = _ => solveDistance10
	| |- _ = DistanceTimes _ _ _ => solveDistance10

	| |- Distance _ _ = _ => solveDistance10
	| |- _ = Distance _ _ => solveDistance10

	| |- IsDistance ?d => immIsDistance2 d

	| |- Supplementary _ _ = _ => solveSupplementary10 || (apply SupplementarySym; solveSupplementary10)
	| |- _ = Supplementary _ _ => solveSupplementary10 || (apply SupplementarySym; solveSupplementary10)

	| |-  Supplement _ _ _ _ _ _ => immSupplement10 
	| |-  OpposedAngles _ _ _ _ _ =>  apply OpposedAngleDef; immBetween8 

	| |- Angle _ _ _ _ _ = _ => solveAngle10
	| |-  _ = Angle _ _ _ _ _ => solveAngle10

	| |- CongruentAngle _ _ _ _ _ _ => immCongruentAngle10
	| |- NullAngle _ _ _ => immNullAngle6
	| |- ElongatedAngle _ _ _ => immElongatedAngle6
	| |- RightAngle _ _ _ => immRightAngle10
	| |- ~NullAngle _ _ _ => immNotNullAngle10
	| |- ~ElongatedAngle _ _ _ => immNotElongatedAngle10
	| |- ~RightAngle _ _ _ => immNotRightAngle10

	| |- IsAngle _ => immIsAngle10

	| |- _ = _ => solveEq9
	| |- _ <> _ => immDistinct10
	| |- ?A = ?B -> False => fold(A <> B); immDistinct10

	| |- Clockwise _ _ _ => immClockwise10
	| |- ~Clockwise _ _ _  => immNotClockwise10
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise10

	| |- Collinear _ _ _ => immCollinear9
	| |- ~Collinear _ _ _  => immNotCollinear10
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear10

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
	| |- OnLine _ _ => immOnLine10

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

Ltac byDefEqPoint10 := match goal with
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
end.

Ltac stepEqDistance10 H  := 
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

	| _ = _ => rewrite H || rewrite <- H
end; try immediate10.

Ltac stepEq10 X Y H  := match type of H with
	| Point => match goal with
			| |- X = Vv => byDefEqPoint10
			| |- Vv = Y  => byDefEqPoint10
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

Ltac stepRightAngle10 A B C H  := match type of H with
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
end.

Ltac stepSupplement10 A B C D E F H := match type of H with 
	| Supplement A B C ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8
	| Supplement C B A ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8
	| Supplement ?K ?L ?M A B C => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8
	| Supplement ?K ?L ?M C B A => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8

	| Supplement D E F ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8
	| Supplement F E D ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8
	| Supplement ?K ?L ?M D E F => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8
	| Supplement ?K ?L ?M F E D => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8

	| CongruentAngle A B C ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8
	| CongruentAngle C B A ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8
	| CongruentAngle ?K ?L ?M A B C => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8
	| CongruentAngle ?K ?L ?M C B A => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate8

	| CongruentAngle D E F ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8
	| CongruentAngle F E D ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8
	| CongruentAngle ?K ?L ?M D E F => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8
	| CongruentAngle ?K ?L ?M F E D => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate8

	| NullAngle A B C => apply NullElongatedSupplement; try immediate8
	| NullAngle C B A => apply NullElongatedSupplement; try immediate8
	| NullAngle D E F => apply  SupplementSym; apply NullElongatedSupplement; try immediate8
	| NullAngle F E D => apply  SupplementSym; apply NullElongatedSupplement; try immediate8

	| ElongatedAngle A B C => apply  SupplementSym; apply NullElongatedSupplement; try immediate8
	| ElongatedAngle C B A => apply  SupplementSym; apply NullElongatedSupplement; try immediate8
	| ElongatedAngle D E F =>  apply NullElongatedSupplement; try immediate8
	| ElongatedAngle F E D => apply NullElongatedSupplement; try immediate8
	
	| RightAngle _ _ _ =>  apply RightRightSupplement; try immediate10

end.

Ltac stepCongruentAngle10 A B C D E F H := match goal with 
	| |- CongruentAngle A B C A B C => apply (CongruentAngleRefl A B C); try immediate8
	| |- CongruentAngle A B C C B A => apply (CongruentAnglePerm A B C); try immediate8

	| |- CongruentAngle _ B _ _ B _  => match type of H with
		| OpenRay B _ _  => apply CongruentAngleSides; try immediate8
		| ClosedRay B _ _  => apply CongruentAngleSides; try immediate8
		| Segment B _ _  => apply CongruentAngleSides; try immediate8
		| Segment _ B _  => apply CongruentAngleSides; try immediate8
		| Between B _ _  => apply CongruentAngleSides; try immediate8
		| Between _ _ B  => apply CongruentAngleSides; try immediate8
		| EquiOriented B _ B _  => apply CongruentAngleSides; try immediate8
	
		| CongruentAngle _ _ _ _ _ _ => stepCongruentTransAngle6 A B C D E F H
	
		| RightAngle _ _ _ =>  apply (RightCongruentAngle A B C D E F); try immediate10

		| TCongruent (Tr B ?X ?Y)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?X B ?Y)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X B Y K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?X ?Y B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X L M K);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent  (Tr ?K ?L ?M) (Tr B ?X ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L Y B X );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?K ?L ?M)  (Tr ?X B ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M X B Y);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent  (Tr ?K ?L ?M)  (Tr ?X ?Y B)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K Y B X);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles1 (Tr ?X B ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X B Y X Y B);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles1 (Tr ?X ?Y B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle X Y B X B Y);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles2 (Tr B ?X ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X Y B X B Y);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles2 (Tr ?X ?Y B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X Y X B);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles3 (Tr B ?X ?Y) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X Y X B);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles3 (Tr ?X B ?Y) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y X B Y B X);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Equilateral (Tr B ?X ?Y) => assert (CongruentAngle X Y B X B Y);
			assert (CongruentAngle Y B X Y X B); try immediate8
		| Equilateral (Tr ?X B ?Y) =>assert (CongruentAngle X B Y X Y B);
			assert (CongruentAngle Y X B Y B X); try immediate8
		| Equilateral (Tr ?X ?Y B) => assert (CongruentAngle X Y B X B Y);
			assert (CongruentAngle Y B X Y X B); try immediate8

		| Supplement A B C ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement C B A ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M A B C => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M C B A => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8

		| Supplement D E F ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement F E D ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M D E F => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M F D E => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8

		| ?X = ?Y => rewrite H || rewrite <- H

		| _ => eqToCongruent8; try immediate8
	end

	| _ => match type of  H with
		| CongruentAngle _ _ _ _ _ _ => stepCongruentTransAngle6 A B C D E F H
	
		| RightAngle _ _ _ =>  apply (RightCongruentAngle A B C D E F); try immediate10

		| TCongruent (Tr B ?X ?Y)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?X B ?Y)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X B Y K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?X ?Y B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X L M K);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent  (Tr ?K ?L ?M) (Tr B ?X ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L Y B X );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?K ?L ?M)  (Tr ?X B ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M X B Y);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent  (Tr ?K ?L ?M)  (Tr ?X ?Y B)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K Y B X);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| TCongruent (Tr E ?X ?Y)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y E X M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?X E ?Y)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X E Y K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?X ?Y E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y E X L M K);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent  (Tr ?K ?L ?M) (Tr E ?X ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L Y E X );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent (Tr ?K ?L ?M)  (Tr ?X E ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M X E Y);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| TCongruent  (Tr ?K ?L ?M)  (Tr ?X ?Y E)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K Y E X);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles1 (Tr ?X B ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X B Y X Y B);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles1 (Tr ?X ?Y B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle X Y B X B Y);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles2 (Tr B ?X ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X Y B X B Y);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles2 (Tr ?X ?Y B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X Y X B);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles3 (Tr B ?X ?Y) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y B X Y X B);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles3 (Tr ?X B ?Y) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y X B Y B X);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles1 (Tr ?X E ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X E Y X Y E);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles1 (Tr ?X ?Y E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle X Y E X E Y);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles2 (Tr E ?X ?Y) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle X Y E X E Y);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles2 (Tr ?X ?Y E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y E X Y X E);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Isosceles3 (Tr E ?X ?Y) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y E X Y X E);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
		| Isosceles3 (Tr ?X E ?Y) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle Y X E Y E X);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

		| Equilateral (Tr B ?X ?Y) => assert (CongruentAngle X Y B X B Y);
			assert (CongruentAngle Y B X Y X B); try immediate8
		| Equilateral (Tr ?X B ?Y) =>assert (CongruentAngle X B Y X Y B);
			assert (CongruentAngle Y X B Y B X); try immediate8
		| Equilateral (Tr ?X ?Y B) => assert ( CongruentAngle X Y B X B Y);
			assert (CongruentAngle Y B X Y X B); try immediate8
		| Equilateral (Tr E ?X ?Y) => assert (CongruentAngle X Y E X E Y);
			assert (CongruentAngle Y E X Y X E); try immediate8
		| Equilateral (Tr ?X E ?Y) =>assert (CongruentAngle X E Y X Y E);
			assert (CongruentAngle Y X E Y E X); try immediate8
		| Equilateral (Tr ?X ?Y E) => assert ( CongruentAngle X Y E X E Y);
			assert (CongruentAngle Y E X Y X E); try immediate8

		| Supplement A B C ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement C B A ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M A B C => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M C B A => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8

		| Supplement D E F ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement F E D ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M D E F => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
		| Supplement ?K ?L ?M F D E => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8

		| ?X = ?Y => rewrite H || rewrite <- H

		| _ => eqToCongruent8; try immediate8
	end
end.

Ltac step10 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance10 H
	| |- _ = DistancePlus _ _  => stepEqDistance10 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance10 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance10 H
	| |- Distance _ _ = _ => stepEqDistance10 H
	| |- _ = Distance _ _ => stepEqDistance10 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |-  Supplement ?A ?B ?C ?D ?E ?F => stepSupplement10 A B C D E F H
	| |-  OpposedAngles ?A ?B ?C ?D ?E => stepOpposed8 A B C D E H

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent10; try immediate10
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent10; try immediate10

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle8 A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle8 A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle8 A B C H
	| |- RightAngle ?A ?B ?C => stepRightAngle10 A B C H

	| |- _ = H => try unfold H; byDefEqPoint10
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint10

	| |- ?A = ?B => stepEq10 A B H
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

Ltac since10 txt := assert txt; try immediate10.

Ltac from10 H txt := assert txt; [(step10 H ; try immediate10) |  try immediate10].

Ltac as10 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate10 | (step10 Hyp ; try immediate10)]).
