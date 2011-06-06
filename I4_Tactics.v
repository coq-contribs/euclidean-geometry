
Ltac setSupplementary8 alpha beta := match goal with
| H : IsAngle alpha |- _ =>  pose (beta := Supplementary alpha H);
					let Hyp := fresh in 
						(assert (Hyp := IsAngleSupplementary alpha H); fold beta in Hyp)
|  _ =>  let H := fresh in (
			assert (H : IsAngle alpha);
			[try immediate7 | pose (beta := Supplementary alpha H);
				let Hyp := fresh in 
					(assert (Hyp := IsAngleSupplementary alpha H); fold beta in Hyp)])
end.

Ltac immIsAngle8 := match goal with
	| H : IsAngle ?alpha |- IsAngle ?alpha => exact H

	| |- IsAngle Uu => apply IsAngleNullAngle
	| |- IsAngle uU => apply IsAngleElongatedAngle

	| |- IsAngle (Angle _ _ _ _ _) =>  apply IsAngleAngle
	| |- IsAngle (Supplementary _ _) =>  apply IsAngleSupplementary

	| |- IsAngle _ => unfold IsAngle; simplCircle2; split; immediate5
end.

Ltac simplDistance8 := intros; splitIsAngle6; simplCircle2; repeat 
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

Ltac solveDistance8 := simplDistance8; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus7
	| |- _ = DistancePlus _ _ => solveDistPlus7

	| |- DistanceTimes _ _ _ = _ => solveDistTimes7
	| |- _ = DistanceTimes _ _ _ => solveDistTimes7

	| |- Distance _ _ = _ => solveDist7
	| |- _ = Distance _ _ => apply sym_eq; solveDist7

	| |- _ => solveEq5
end.

Ltac immDistinct8 := match goal with
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

Ltac immBetween8 :=  match goal with
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

	| |- Between ?B _ _ => unfold B; immBetween6
	| |- Between _ ?B _ => unfold B; immBetween6
	| |- Between _ _ ?B => unfold B; immBetween6
end.

Ltac immSegment8 := match goal with
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

	| |- Segment _ _ _  => apply BetweenSegment; immBetween8
	| |- Segment _ _ _  =>  apply SegmentSym; apply BetweenSegment ; immBetween8

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immCongruentAngle8 := match goal with 
	| |- CongruentAngle ?A ?B ?C ?A ?B ?C => apply (CongruentAngleRefl A B C); try  immDistinct6
	| |- CongruentAngle ?A ?B ?C ?C ?B ?A => apply (CongruentAnglePerm A B C); try  immDistinct6

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

	| H : OpposedAngles ?A ?B ?C ?D ?E |- CongruentAngle _ ?A _ _ ?A _ => orderAngle7  B A C D A E; apply OpposedCongruentAngles; immediate6
end.

Ltac immSupplement8 := match goal with
	|  |- Supplement Uu Oo Uu Uu Oo uU => exact SupplementUuuU
	|  |- Supplement Uu Oo Uu uU Oo Uu =>  apply SupplementRev2; exact SupplementUuuU
	|  |- Supplement Uu Oo uU Uu Oo Uu => apply SupplementSym; exact SupplementUuuU
	|  |- Supplement uU Oo Uu Uu Oo Uu =>  apply SupplementSym; apply SupplementRev2; exact SupplementUuuU
 
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?A ?B ?C ?D ?E ?F => exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?C ?B ?A ?D ?E ?F =>  apply SupplementRev1; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?A ?B ?C ?F ?E ?D => apply SupplementRev2; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?C ?B ?A ?F ?E ?D =>  apply SupplementRev1; apply SupplementRev2; exact H
 
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?D ?E ?F ?A ?B ?C=>  apply SupplementSym; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?D ?E ?F ?C ?B ?A=>   apply SupplementSym; apply SupplementRev1; exact H 
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?F ?E ?D ?A ?B ?C=>  apply SupplementSym; apply SupplementRev2; exact H
	| H : Supplement ?A ?B ?C ?D ?E ?F |- Supplement ?F ?E ?D ?C ?B ?A=>   apply SupplementSym; apply SupplementRev1; apply SupplementRev2; exact H

	| H : Between ?B ?A ?D |- Supplement ?B ?A ?C ?C ?A ?D => apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?B ?C ?A ?D => apply SupplementRev1; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?B ?A ?C ?D ?A ?C => apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?B ?D ?A ?C => apply SupplementRev1; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]

	| H : Between ?B ?A ?D |- Supplement ?C ?A ?D ?B ?A ?C => apply SupplementSym; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?D ?C ?A ?B => apply SupplementSym; apply SupplementRev1; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?D ?A ?C ?B ?A ?C => apply SupplementSym; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
	| H : Between ?B ?A ?D |- Supplement ?D ?A ?C ?C ?A ?B => apply SupplementSym; apply SupplementRev1; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct8 | exact H]
end.

Ltac supplementAngleHef8 A B C D E F Hba Hbc Hed Hef := match goal with
	| Hef : E <> F |- _  =>  apply (EqAngleSupplement A B C D E F Hba Hbc Hed Hef)
	| _ =>  let Hef := fresh in (assert (Hef : E <> F); [try immediate5 |  apply (EqAngleSupplement A B C D E F Hba Hbc Hed Hef)])
end.

Ltac supplementAngleHed8 A B C D E F Hba Hbc Hed := match goal with
	| Hef : E <> F |- _  =>  supplementAngleHef8 A B C D E F Hba Hbc Hed Hef
	| _ =>  let Hef := fresh in (assert (Hef : E <> F); [try immediate5 |  supplementAngleHef8 A B C D E F Hba Hbc Hed Hef])
end.

Ltac supplementAngleHbc8 A B C D E F Hba Hbc:= match goal with
	| Hed : E <> D |- _  =>  supplementAngleHed8 A B C D E F Hba Hbc Hed
	| _ =>  let Hed := fresh in (assert (Hed : E <> D); [try immediate5 |  supplementAngleHed8 A B C D E F Hba Hbc Hed])
end.

Ltac supplementAngleHba8 A B C D E F Hba := match goal with
	| Hbc : B <> C |- _  =>  supplementAngleHbc8 A B C D E F Hba Hbc
	| _ =>  let Hbc := fresh in (assert (Hbc : B <> C); [try immediate5 |  supplementAngleHbc8 A B C D E F Hba Hbc])
end.

Ltac congruentToEq8 := unfold NullAngle, ElongatedAngle in *;
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

Ltac eqToCongruent8 := repeat match goal with
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Angle ?D ?E ?F ?Hed ?Hef  |- _ => let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C D E F Hba Hbc Hed Hef H)); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef)  |- _ => let Hyp := fresh in assert (Hyp := (EqAngleSupplement A B C D E F Hba Hbc Hed Hef H)); clear H
	| H : Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef) = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (EqAngleSupplement A B C D E F Hba Hbc Hed Hef (sym_eq H))); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = Uu  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc H)); clear H
	| H : Uu = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc (sym_eq H))); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = uU  |- _ => let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc H)); clear H
	| H : uU = Angle ?A ?B ?C ?Hba ?Hbc  |- _ =>  let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc (sym_eq H))); clear H

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

	| H : IsAngle ?alpha  |- Angle ?A ?B ?C ?Hba ?Hbc = ?alpha => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H); apply EqCongruentAngle
	| H : IsAngle ?alpha |- ?alpha = Angle ?A ?B ?C ?Hba ?Hbc => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H); apply EqCongruentAngle

	| _ => idtac
end.

Ltac solveAngle8 := match goal with 
	| |- Angle _ _ _ _ _ = Angle _ _ _ _ _ => apply EqCongruentAngle; immCongruentAngle8

	| |- Angle _ _ _ _ _ = Supplementary  _ _ => apply SupplementSupplementary; immSupplement8
	| |- Supplementary  _ _ = Angle _ _ _ _ _  => apply sym_eq; apply SupplementSupplementary; immSupplement8

	| |- Angle ?A ?B ?C _ _ = Uu => eqToCongruent8; immNullAngle6
	| |- Uu = Angle ?A ?B ?C _ _ => eqToCongruent8; immNullAngle6

	| |- Angle ?A ?B ?C _ _ = uU => eqToCongruent8; immElongatedAngle6
	| |- uU = Angle ?A ?B ?C _ _ => eqToCongruent8; immElongatedAngle6

	| |- Angle Uu Oo ?M _ _ = ?M => apply EqAnglePoint; immIsAngle6
	| |- ?M = Angle Uu Oo ?M _ _  => apply sym_eq; apply EqAnglePoint; immIsAngle6
	| |- Angle ?M Oo Uu ?H1 ?H2 = ?M => rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2));  apply EqAnglePoint; immIsAngle6
	| |- ?M = Angle ?M Oo Uu ?H1 ?H2  => apply sym_eq;  rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2)); apply EqAnglePoint; immIsAngle6

end.

Ltac solveSupplementary8 := match goal with
	| |- Supplementary _ _ = Supplementary _ _ => apply SupplementaryEqAngles; solveSupplementary8
	| |- Supplementary (Supplementary _ _) _ = _ => rewrite SupplementarySupplementary; solveSupplementary8
	| |- _ = Supplementary (Supplementary _ _) _ => rewrite SupplementarySupplementary; solveSupplementary8

	| |- Supplementary Uu _ = _ => rewrite SupplementaryNullAngle; solveSupplementary8	| |- _ = Supplementary Uu _  => rewrite SupplementaryNullAngle; solveSupplementary8	| |- Supplementary uU _ = _ => rewrite SupplementaryElongatedAngle; solveSupplementary8	| |- _ = Supplementary uU _  => rewrite SupplementaryElongatedAngle; solveSupplementary8	

	| |- _ = _ => solveAngle8
end.

Ltac immediate8 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate8
	| |- ?A \/ ?B => (left; immediate8)  || (right; immediate8)

	| |- DistancePlus _ _ = _ => solveDistance8
	| |- _ = DistancePlus _ _ => solveDistance8

	| |- DistanceTimes _ _ _ = _ => solveDistance8
	| |- _ = DistanceTimes _ _ _ => solveDistance8

	| |- Distance _ _ = _ => solveDistance8
	| |- _ = Distance _ _ => solveDistance8

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

	| |- _ = _ => solveEq7
	| |- _ <> _ => immDistinct8
	| |- ?A = ?B -> False => fold(A <> B); immDistinct8

	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise6
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise3

	| |- Collinear _ _ _ => immCollinear6
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1

	| |- EquiOriented _ _ _ _ => immEquiOriented5
	| |- OpenRay _ _ _ => immOpenRay6
	| |- ClosedRay _ _ _ => immClosedRay6
	| |- Between _ _ _ => immBetween8
	| |- Segment _ _ _ => immSegment8

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

Ltac stepBetweenSupplement8 A B C D := first
	[assert (~Clockwise C B A); [immediate8 | apply (ClockwiseSupplementAnglesBetween B A C D); try immediate8] |
	assert (~Clockwise D B C); [immediate8 | apply (ClockwiseSupplementAnglesBetween B A C D); try immediate8] |
	assert (~Clockwise A B C); [immediate8 | apply (AntiClockwiseSupplementAnglesBetween B A C D);  try immediate8] |
	assert (~Clockwise C B D); [immediate8 | apply (AntiClockwiseSupplementAnglesBetween B A C D);  try immediate8]].

Ltac stepBetweenOpposed8 A B C D E :=  first
	[assert (~Clockwise C B A); [immediate8 | apply (OpposedAnglesAntiClockwiseBetween B C A E D); try immediate8] |
	assert (~Clockwise E B D); [immediate8 | apply (OpposedAnglesAntiClockwiseBetween B C A E D); try immediate8] |
	assert (~Clockwise A B C); [immediate8 | apply (OpposedAnglesClockwiseBetween B C A E D);  try immediate8] |
	assert (~Clockwise D B E); [immediate8 | apply (OpposedAnglesClockwiseBetween B C A E D);  try immediate8]].

Ltac stepBetween8 A B D H := match type of H with

	| Segment A D B => apply SegmentBetween; try immediate8
	| Segment D A B => apply BetweenSym; apply SegmentBetween; try immediate8

	| OpenRay B ?C D => apply (OpenRayBetween A B C D H); try immediate8
	| ClosedRay B D ?C => apply (OpenRayBetween A B C D); try immediate8
	| OpenRay B D ?C => apply (OpenRayBetween A B C D H); try immediate8
	| ClosedRay B ?C D => apply (OpenRayBetween A B C D); try immediate8
	| EquiOriented B ?C B D => apply (OpenRayBetween A B C D); try immediate8
	| OpenRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate8
	| ClosedRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate8
	| OpenRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate8
	| ClosedRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate8
	| EquiOriented B ?C B A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate8

	| Between A B ?C => apply (OpenRayBetween A B C D); try immediate8
	| Between ?C B A => apply (OpenRayBetween A B C D); try immediate8
	| Between D B ?C => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate8
	| Between ?C B D => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate8
	| Segment A ?C B => apply (OpenRayBetween A B C D); try immediate3
	| Segment ?C A B => apply (OpenRayBetween A B C D); try immediate3
	| Segment D ?C B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3
	| Segment ?C D B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3

	| Between ?E B ?F => apply (OpenRaysBetween B E F A D H); try immediate3

	| Supplement ?C B D A B ?C  => stepBetweenSupplement8 A B C D
	| Supplement A B ?C ?C B D   => stepBetweenSupplement8 A B C D
	| Supplement D B ?C A B ?C => stepBetweenSupplement8 A B C D
	| Supplement A B ?C D B ?C => stepBetweenSupplement8 A B C D
	| Supplement ?C B D ?C B A => stepBetweenSupplement8 A B C D
	| Supplement ?C B A ?C B D  => stepBetweenSupplement8 A B C D
	| Supplement D B ?C ?C B A   => stepBetweenSupplement8 A B C D
	| Supplement ?C B A  D B ?C  => stepBetweenSupplement8 A B C D

	| CongruentAngle ?C B A  D B ?E  => stepBetweenOpposed8 A B C D E
	| CongruentAngle A B ?C D B ?E  => stepBetweenOpposed8 A B C D E
	| CongruentAngle ?C B A ?E B D => stepBetweenOpposed8 A B C D E
	| CongruentAngle A B ?C ?E B D  => stepBetweenOpposed8 A B C D E
	| CongruentAngle D B ?E  ?C B A  => stepBetweenOpposed8 A B C D E
	| CongruentAngle D B ?E A B ?C  => stepBetweenOpposed8 A B C D E
	| CongruentAngle ?E B D ?C B A => stepBetweenOpposed8 A B C D E
	| CongruentAngle ?E B D A B ?C  => stepBetweenOpposed8 A B C D E

	| Point => match H with
		| uU => apply ElongatedAngleBetween
		end

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate8
end.

Ltac stepSegment8 A B C H := match type of H with

	| EquiOriented C B A ?D => apply (EquiOrientedClosedRaySegment A D C B H); try immediate8
	| ClosedRay A ?D C => apply (EquiOrientedClosedRaySegment A D C B); [try immediate8 | exact H]

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate8

	| _ => apply EquiOrientedSegment; stepEquiOriented1 A C C B H
end.

Ltac stepEq8 X Y H  := match type of H with
	| Point => match goal with
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

Ltac stepSupplement8 A B C D E F H := match type of H with 
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

end.

Ltac stepOpposed8 A B C D E H := match type of H  with
	| ~Clockwise B A C => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	| ~Clockwise A C B => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise C B A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise A B C => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise B C A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise C A B => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8

	|  ~Clockwise D A E => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise A E D => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise E D A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise A D E => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise D E A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise E A D => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate8

	|  Clockwise B A C => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise A C B => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise C B A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise A B C => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise B C A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise C A B => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8

	|  Clockwise D A E => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise A E D=> apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  Clockwise E D A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise A D E => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise D E A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
	|  ~Clockwise E A D => apply ClockwiseBetweenCongruentOpposedAngles; try immediate8
end.

Ltac stepCongruentAngle8 A B C D E F H :=  match type of H with
	| OpenRay B A D  => apply CongruentAngleSides; try immediate8
	| OpenRay B A F  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| OpenRay B C D  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| OpenRay B C F  => apply CongruentAngleSides; try immediate8
	| OpenRay B D A  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| OpenRay B F A  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| OpenRay B D C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| OpenRay B F C  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8

	| ClosedRay B A D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| ClosedRay B A F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| ClosedRay B C D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| ClosedRay B C F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| ClosedRay B D A  => apply CongruentAngleSides; try immediate8
	| ClosedRay B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| ClosedRay B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| ClosedRay B F C  => apply CongruentAngleSides; try immediate8

	| Segment B A D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| Segment B A F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment B C D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment B C F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| Segment B D A  => apply CongruentAngleSides; try immediate8
	| Segment B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment B F C  => apply CongruentAngleSides; try immediate8

	| Segment A B D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| Segment A B F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment C B D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment C B F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| Segment D B A  => apply CongruentAngleSides; try immediate8
	| Segment F B A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment D B C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Segment F B C  => apply CongruentAngleSides; try immediate8

	| Between B A D  =>apply CongruentAngleSides; try immediate8
	| Between B A F  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between B C D  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between B C F  =>apply CongruentAngleSides; try immediate8
	| Between B D A  => apply CongruentAngleSides; try immediate8
	| Between B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between B F C  => apply CongruentAngleSides; try immediate8

	| Between A D B  =>apply CongruentAngleSides; try immediate8
	| Between A F B  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between C D B  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between C F B  =>apply CongruentAngleSides; try immediate8
	| Between D A B  => apply CongruentAngleSides; try immediate8
	| Between F A B  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between D C B  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| Between F C B  => apply CongruentAngleSides; try immediate8

	| EquiOriented B A B D  => apply CongruentAngleSides; try immediate8
	| EquiOriented B A B F  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| EquiOriented B C B D  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| EquiOriented B C B F  => apply CongruentAngleSides; try immediate8
	| EquiOriented B D B A  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	| EquiOriented B F B A  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| EquiOriented B D B C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate8
	| EquiOriented B F B C  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate8
	
	| CongruentAngle _ _ _ _ _ _ => stepCongruentTransAngle6 A B C D E F H
	| NullAngle _ _ _ => apply (NullCongruentAngle A B C D E F) ; try immediate6
	| ElongatedAngle _ _ _  => apply (ElongatedCongruentAngle A B C D E F) ; try immediate6
	
	| OpposedAngles  ?J ?K ?L ?M ?N => let Hyp := fresh in (
						assert (Hyp := OpposedCongruentAngles J K L M N H); 
						stepCongruentTransAngle6 A B C D E F Hyp)

	| TCongruent (Tr B A C)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr B C A)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr A B C)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr C B A)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr C A B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C L M K);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr A C B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A L M K);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr B A C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L C B A );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr B C A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L A B C );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr A B C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M A B C);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr C B A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M C B A);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr A C B)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K C B A);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr C A B)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K A B C);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| TCongruent (Tr E D F)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr E F D)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F M K L);
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr D E F)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr F E D)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D K L M);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr D F E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D L M K);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr F D E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F L M K);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr E F D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L D E F );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr E D F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L F E D );
			[ apply TCongruentAnglesA; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr D E F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M D E F);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr F E D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M F E D);
			[ apply TCongruentAnglesB; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr D F E)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K F E D);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr F D E)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K D E F);
			[ apply TCongruentAnglesC; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles1 (Tr A B C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C A C B);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr C B A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A C A B);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr A C B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A C B A B C);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr C A B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C A B C B A);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles2 (Tr B A C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A C B A B C);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr B C A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C A B C B A);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr A C B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A C A B);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr C A B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C A C B);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles3 (Tr B A C) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A C A B);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr B C A) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C A C B);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr A B C) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C A B C B A);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr C B A) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A C B A B C);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles1 (Tr D E F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F D F E);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr F E D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D F D E);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr D F E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D F E D E F);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles1 (Tr F D E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F D E F E D);
			[ apply IsoscelesEqAngles1; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles2 (Tr E D F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D F E D E F);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr E F D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F D E F E D);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr D F E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D F D E);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles2 (Tr F D E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F D F E);
			[ apply IsoscelesEqAngles2; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Isosceles3 (Tr E D F) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D F D E);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr E F D) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F D F E);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr D E F) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F D E F E D);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])
	| Isosceles3 (Tr F E D) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D F E D E F);
			[ apply IsoscelesEqAngles3; try immediate8 | stepCongruentAngle7 A B C D E F Hyp])

	| Equilateral (Tr B A C) => assert (CongruentAngle A C B A B C);
			assert (CongruentAngle C B A C A B); try immediate8
	| Equilateral (Tr B C A) => assert (CongruentAngle C A B C B A);
			assert (CongruentAngle A B C A C B); try immediate8
	| Equilateral (Tr A B C) =>assert (CongruentAngle A B C A C B);
			assert (CongruentAngle C A B C B A); try immediate8
	| Equilateral (Tr C B A) =>assert (CongruentAngle C B A C A B);
			assert (CongruentAngle A C B A B C); try immediate8
	| Equilateral (Tr A C B) => assert ( CongruentAngle A C B A B C);
			assert (CongruentAngle C B A C A B); try immediate8
	| Equilateral (Tr C A B) => assert ( CongruentAngle C A B C B A);
			assert (CongruentAngle A B C A C B); try immediate8

	| Equilateral (Tr E D F) => assert (CongruentAngle D F E D E F);
			assert (CongruentAngle F E D F D E); try immediate8
	| Equilateral (Tr E F D) => assert (CongruentAngle F D E F E D);
			assert (CongruentAngle D E F D F E); try immediate8
	| Equilateral (Tr D E F) =>assert (CongruentAngle D E F D F E);
			assert (CongruentAngle F D E F E D); try immediate8
	| Equilateral (Tr F E D) =>assert (CongruentAngle F E D F D E);
			assert (CongruentAngle D F E D E F); try immediate8
	| Equilateral (Tr D F E) => assert ( CongruentAngle D F E D E F);
			assert (CongruentAngle F E D F D E); try immediate8
	| Equilateral (Tr F D E) => assert ( CongruentAngle F D E F E D);
			assert (CongruentAngle D E F D F E); try immediate8

	| Supplement A B C ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
	| Supplement C B A ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
	| Supplement ?K ?L ?M A B C => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
	| Supplement ?K ?L ?M C B A => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8

	| Supplement D E F ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
	| Supplement F E D ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
	| Supplement ?K ?L ?M D E F => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8
	| Supplement ?K ?L ?M F D E => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate8

	| ?X = ?Y => rewrite H || rewrite <- H

	
	| _ => eqToCongruent6; try immediate8
end.

Ltac stepNullAngle8 A B C H :=  match type of H with
	| _ <> _  => apply (OpenRayNullAngle B A C);  try immediate8
	| OpenRay _ _ _  => apply (OpenRayNullAngle B A C);  try immediate8
	| ClosedRay _ _ _  => apply (OpenRayNullAngle B A C);  try immediate8

	| NullAngle ?D ?E ?F => apply (CongruentNullAngle D E F A B C H); try immediate8

	| CongruentAngle ?D ?E ?F A B C => apply (CongruentNullAngle D E F A B C); try immediate8
	| CongruentAngle ?D ?E ?F C B A => apply (CongruentNullAngle D E F A B C); try immediate8
	| CongruentAngle A B C ?D ?E ?F => apply (CongruentNullAngle D E F A B C); try immediate8
	| CongruentAngle C B A ?D ?E ?F => apply (CongruentNullAngle D E F A B C); try immediate8

	| ElongatedAngle ?D ?E ?F => apply (ElongatedSupplementNull A B C D E F H); try immediate8

	| Supplement A B C ?D ?E ?F => apply (ElongatedSupplementNull A B C D E F); try immediate8
	| Supplement C B A ?D ?E ?F => apply (ElongatedSupplementNull A B C D E F); try immediate8
	| Supplement ?D ?E ?F A B C => apply (ElongatedSupplementNull A B C D E F); try immediate8
	| Supplement ?D ?E ?F C B A => apply (ElongatedSupplementNull A B C D E F); try immediate8

end.

Ltac stepElongatedAngle8 A B C H :=  match type of H with
	| ElongatedAngle ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C H); try immediate8

	| CongruentAngle ?D ?E ?F A B C => apply (CongruentElongatedAngle D E F A B C); try immediate8
	| CongruentAngle ?D ?E ?F C B A => apply (CongruentElongatedAngle D E F A B C); try immediate8
	| CongruentAngle A B C ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C); try immediate8
	| CongruentAngle C B A ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C); try immediate8

	| Segment A C B => apply BetweenElongatedAngle; try immediate6
	| Segment C A B => apply BetweenElongatedAngle; try immediate6

	| NullAngle ?D ?E ?F => apply (NullSupplementElongated D E F A B C H); try immediate8

	| Supplement A B C ?D ?E ?F => apply (NullSupplementElongated D E F A B C); try immediate8
	| Supplement C B A ?D ?E ?F => apply (NullSupplementElongated D E F A B C); try immediate8
	| Supplement ?D ?E ?F A B C => apply (NullSupplementElongated D E F A B C); try immediate8
	| Supplement ?D ?E ?F C B A => apply (NullSupplementElongated D E F A B C); try immediate8
end.

Ltac step8 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance7 H
	| |- _ = DistancePlus _ _  => stepEqDistance7 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance7 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance7 H
	| |- Distance _ _ = _ => stepEqDistance7 H
	| |- _ = Distance _ _ => stepEqDistance7 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |-  Supplement ?A ?B ?C ?D ?E ?F => stepSupplement8 A B C D E F H
	| |-  OpposedAngles ?A ?B ?C ?D ?E => stepOpposed8 A B C D E H

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent8; try immediate8
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent8; try immediate8

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle8 A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle8 A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle8 A B C H

	| |- _ = H => try unfold H; byDefEqPoint5
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint5

	| |- ?A = ?B => stepEq8 A B H
	| |- ?A <> ?B => stepDistinct3 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct3 A B H

	| |- Collinear _ _ _  => stepCollinear6 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented1 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay6 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay6 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise3 A B C H
	| |- Between ?A ?B ?D => stepBetween8 A B D H
	| |- Segment ?A ?B ?C  => stepSegment8 A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec2 A B C D E F H

	| |- TStrict ?t => stepTStrict7 t H

	| |- TCongruent _ _ => stepTCongruent7 H

end.

Ltac since8 txt := assert txt; try immediate8.

Ltac from8 H txt := assert txt; [(step8 H ; try immediate8) |  try immediate8].

Ltac as8 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate8 |( step8 Hyp ; try immediate8)]).
