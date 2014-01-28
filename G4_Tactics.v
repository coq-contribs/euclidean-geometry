Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B6_EquiDirectedProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics .
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F4_ArchimedianDistance F5_Tactics .
Require Import G1_Angles G2_AngleProp G3_ParticularAngle.


Ltac setAngle6 A B C alpha := match goal with
| Hba : B <> A, Hbc : B <> C |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B = A -> False, Hbc : B <> C |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B <> A, Hbc : B = C -> False |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B = A -> False, Hbc : B = C -> False |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B <> A |- _ =>  let Hbc := fresh in (
				assert (Hbc : B <> C);
				[try immediate5 | pose (alpha := Angle A B C Hba Hbc)])
| Hba : B = A -> False |- _ =>  let Hbc := fresh in (
				assert (Hbc : B <> C);
				[try immediate5 | pose (alpha := Angle A B C Hba Hbc)])
| Hbc : B <> C |- _ =>  let Hba := fresh in (
				assert (Hba : B <> A);
				[try immediate5 | pose (alpha := Angle A B C Hba Hbc)])
| Hbc : B = C -> False |- _ =>  let Hba := fresh in (
				assert (Hba : B <> A);
				[try immediate5 | pose (alpha := Angle A B C Hba Hbc)])
|  _ =>  let Hba := fresh in (
			assert (Hba : B <> A);
			[try immediate5 | let Hbc := fresh in (
				assert (Hbc : B <> C);
				[try immediate5 | pose (alpha := Angle A B C Hba Hbc)])])
end.

Ltac congruentToEqAngleHef6 A B C D E F Hba Hbc Hed Hef := match goal with
	| Hef : E <> F |- _  =>  apply (CongruentEqAngle A B C D E F Hba Hbc Hed Hef)
	| Hef : E = F -> False |- _  =>  apply (CongruentEqAngle A B C D E F Hba Hbc Hed Hef)
	| _ =>  let Hef := fresh in (assert (Hef : E <> F); [try immediate5 |  apply (CongruentEqAngle A B C D E F Hba Hbc Hed Hef)])
end.

Ltac congruentToEqAngleHed6 A B C D E F Hba Hbc Hed := match goal with
	| Hef : E <> F |- _  =>  congruentToEqAngleHef6 A B C D E F Hba Hbc Hed Hef
	| Hef : E = F -> False |- _  =>  congruentToEqAngleHef6 A B C D E F Hba Hbc Hed Hef
	| _ =>  let Hef := fresh in (assert (Hef : E <> F); [try immediate5 |  congruentToEqAngleHef6 A B C D E F Hba Hbc Hed Hef])
end.

Ltac congruentToEqAngleHbc6 A B C D E F Hba Hbc:= match goal with
	| Hed : E <> D |- _  =>  congruentToEqAngleHed6 A B C D E F Hba Hbc Hed
	| Hed : E = D -> False |- _  =>  congruentToEqAngleHed6 A B C D E F Hba Hbc Hed
	| _ =>  let Hed := fresh in (assert (Hed : E <> D); [try immediate5 |  congruentToEqAngleHed6 A B C D E F Hba Hbc Hed])
end.

Ltac congruentToEqAngleHba6 A B C D E F Hba := match goal with
	| Hbc : B <> C |- _  =>  congruentToEqAngleHbc6 A B C D E F Hba Hbc
	| Hbc : B = C -> False |- _  =>  congruentToEqAngleHbc6 A B C D E F Hba Hbc
	| _ =>  let Hbc := fresh in (assert (Hbc : B <> C); [try immediate5 |  congruentToEqAngleHbc6 A B C D E F Hba Hbc])
end.

Ltac congruentToEq6 := unfold NullAngle, ElongatedAngle in *;
repeat match goal with
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- _ => match goal with
		| Hba : B <> A, Hbc : B <> C, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B <> C, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B = C -> False, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B = C  -> False, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B <> C, Hed : E = D -> False, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B <> C, Hed : E = D -> False, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B = C -> False, Hed : E = D -> False, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B = C  -> False, Hed : E = D -> False, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B <> C, Hed : E <> D, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B <> C, Hed : E <> D, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B = C -> False, Hed : E <> D, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B = C  -> False, Hed : E <> D, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B <> C, Hed : E = D -> False, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B <> C, Hed : E = D -> False, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B <> A, Hbc : B = C -> False, Hed : E = D -> False, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| Hba : B = A -> False, Hbc : B = C  -> False, Hed : E = D -> False, Hef : E = F -> False |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| _ => inversion_clear H
		end
end; 
match goal with
	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => 
		match goal with
			| Hba : B <> A |- _  => congruentToEqAngleHba6 A B C D E F Hba
			| Hba : B = A -> False |- _  => congruentToEqAngleHba6 A B C D E F Hba
			| _ =>  let Hba := fresh in (assert (Hba : B <> A); [try immediate5 | congruentToEqAngleHba6 A B C D E F Hba])
			end 

	| _ => idtac
end.

Ltac eqToCongruent6 := repeat match goal with
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Angle ?D ?E ?F ?Hed ?Hef  |- _ => let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C D E F Hba Hbc Hed Hef H)); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = Uu  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc H)); clear H
	| H : Uu = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc (sym_eq H))); clear H

	| H : Angle ?A ?B ?C ?Hba ?Hbc = uU  |- _ => let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc H)); clear H
	| H : uU = Angle ?A ?B ?C ?Hba ?Hbc  |- _ =>  let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc (sym_eq H))); clear H

	| Ha : IsAngle ?alpha, H : Angle ?A ?B ?C ?Hba ?Hbc = ?alpha |- _ => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha Ha) Ha) in H;  let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C Uu Oo alpha Hba Hbc DistinctOoUu (IsAngleDistinctOo alpha Ha) H)); clear H
	| Ha : IsAngle ?alpha, H : ?alpha = Angle ?A ?B ?C ?Hba ?Hbc |- _ => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha Ha) Ha) in H; let Hyp := fresh in assert (Hyp := (CongruentEqAngle Uu Oo alpha A B C DistinctOoUu (IsAngleDistinctOo alpha Ha) Hba Hbc H)); clear H

end; match goal with
	| |- Angle ?A ?B ?C ?Hba ?Hbc = Angle ?D ?E ?F ?Hed ?Hef => apply (EqCongruentAngle A B C D E F Hba Hbc Hed Hef)

	| |- Angle ?A ?B ?C ?Hba ?Hbc = Uu => apply (EqNullAngle A B C Hba Hbc)
	| |- Uu = Angle ?A ?B ?C ?Hba ?Hbc => apply sym_eq; apply (EqNullAngle A B C Hba Hbc)

	| |- Angle ?A ?B ?C ?Hba ?Hbc = uU => apply (EqElongatedAngle A B C Hba Hbc)
	| |- uU = Angle ?A ?B ?C ?Hba ?Hbc => apply sym_eq; apply (EqElongatedAngle A B C Hba Hbc)

	| H : IsAngle ?alpha  |- Angle ?A ?B ?C ?Hba ?Hbc = ?alpha => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H); apply EqCongruentAngle
	| H : IsAngle ?alpha |- ?alpha = Angle ?A ?B ?C ?Hba ?Hbc => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha H) H); apply EqCongruentAngle

	| _ => idtac
end.

Ltac immIsAngle6 := match goal with
	| H : IsAngle ?alpha |- IsAngle ?alpha => exact H
	| |- IsAngle Uu => apply IsAngleNullAngle
	| |- IsAngle uU => apply IsAngleElongatedAngle
	| |- IsAngle (Angle _ _ _ _ _) =>  apply IsAngleAngle
	| |- IsAngle _ => unfold IsAngle; simplCircle2; split; immediate5
end.

Ltac immDistinct6 := match goal with
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

end.

Ltac immNotClockwise6 := match goal with
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

Ltac immBetween6 :=  match goal with
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

	| |- Between ?B _ _ => unfold B; immBetween6
	| |- Between _ ?B _ => unfold B; immBetween6
	| |- Between _ _ ?B => unfold B; immBetween6
end.

Ltac immSegment6 := match goal with
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

	| |- Segment _ _ _  => apply BetweenSegment; immBetween6
	| |- Segment _ _ _  =>  apply SegmentSym; apply BetweenSegment ; immBetween6

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immOpenRay6 := match goal with 
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

	| |- OpenRay (InterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immOpenRay3
	| |- OpenRay _ (InterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immOpenRay3
	| |- OpenRay _ _ (InterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immOpenRay3

	| |- OpenRay (SecondInterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immOpenRay3
	| |- OpenRay _ (SecondInterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immOpenRay3
	| |- OpenRay _ _ (SecondInterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immOpenRay3

	| |- OpenRay (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immOpenRay3
	| |- OpenRay _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immOpenRay3
	| |- OpenRay _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immOpenRay3

	| |- OpenRay (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immOpenRay3
	| |- OpenRay _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immOpenRay3
	| |- OpenRay _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immOpenRay3

	| |- OpenRay (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immOpenRay3
	| |- OpenRay _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immOpenRay3
	| |- OpenRay _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immOpenRay3

	| |- OpenRay (SymmetricPoint ?A ?B ?H) _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immOpenRay3
	| |- OpenRay _ (SymmetricPoint ?A ?B ?H) _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immOpenRay3
	| |- OpenRay _ _ (SymmetricPoint ?A ?B ?H) => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immOpenRay3

	| |- OpenRay ?A (Graduation _ ?A ?B _) ?B => apply ClosedRayOpenRay; apply GraduationClosedRay

	| H : NullAngle ?B ?A ?C |- OpenRay ?A ?B ?C => apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?C ?A ?B |- OpenRay ?A ?B ?C => apply (NullAngleOpenRay A B C (NullAngleSym B A C H))
end.

Ltac immClosedRay6 := apply OpenRayClosedRay; immOpenRay6.

Ltac immCollinear6 := match goal with
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

Ltac splitIsAngle6 := repeat (match goal with
	| H : IsAngle _ |- _ => unfold IsAngle in H; decompose [and] H
end); repeat (match goal with
	| H : OnCircle uCircle ?beta /\ ~Clockwise Uu ?beta Oo |- _ => fold (IsAngle beta) in H
end).

Ltac simplDistance6 := intros; splitIsAngle6; simplCircle2; repeat 
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

	| H1 : IsDistance ?d,  H2 : context [(Distance Oo ?d)] |- _ => rewrite (IsDistanceEqDistance d H1) in H2
	| H1 : IsDistance ?d |- context [(Distance Oo ?d)] => rewrite (IsDistanceEqDistance d H1) 
	| H1 : IsDistance ?d,  H2 : context [(Distance ?d Oo)] |- _ => rewrite (DistanceSym d Oo) in H2; rewrite (IsDistanceEqDistance d H1) in H2
	| H1 : IsDistance ?d |- context [(Distance ?d Oo)] => rewrite (DistanceSym d Oo); rewrite (IsDistanceEqDistance d H1) 

	| H1 : IsAngle ?alpha,  H2 : context [(Distance Oo ?alpha)] |- _ => rewrite (IsAngleDistance alpha H1) in H2
	| H1 : IsAngle ?alpha |- context [(Distance Oo ?alpha)] => rewrite (IsAngleDistance alpha H1) 
	| H1 : IsAngle ?alpha,  H2 : context [(Distance ?alpha Oo)] |- _ => rewrite (DistanceSym alpha Oo) in H2; rewrite (IsAngleDistance alpha H1) in H2
	| H1 : IsAngle ?alpha |- context [(Distance ?alpha Oo)] => rewrite (DistanceSym alpha Oo); rewrite (IsAngleDistance alpha H1) 

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

	| H : context [(Distance Oo (Angle ?A ?B ?C ?Hba ?Hbc))] |- _ => rewrite DistanceOoAngle  in H
	| |- context [(Distance Oo (Angle ?A ?B ?C ?Hba ?Hbc))] => rewrite DistanceOoAngle  
	| H : context [(Distance (Angle ?A ?B ?C ?Hba ?Hbc) Oo)] |- _ => rewrite (DistanceSym (Angle A B C Hba Hbc) Oo) in H; rewrite DistanceOoAngle  in H
	| |- context [(Distance (Angle ?A ?B ?C ?Hba ?Hbc) Oo)] => rewrite (DistanceSym (Angle A B C Hba Hbc) Oo); rewrite DistanceOoAngle
end).

Ltac solveDistance6 := try simplDistance6; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus2
	| |- _ = DistancePlus _ _ => solveDistPlus2

	| |- DistanceTimes _ _ _ = _ => solveDistTimes2
	| |- _ = DistanceTimes _ _ _ => solveDistTimes2

	| |- Distance _ _ = _ => solveDist2
	| |- _ = Distance _ _ => apply sym_eq; solveDist2

	| |- _ => solveEq5
end.

Ltac immOnCircle6 := match goal with 
	| H : OnCircle ?c ?A |- OnCircle ?c ?A => exact H

	| H : IsAngle ?A |- OnCircle uCircle ?A => unfold IsAngle in H; intuition

	| |- OnCircle ?c (IntersectionCirclesPoint ?c _ _) => apply OnCircle1IntersectionCirclesPoint
	| |- OnCircle ?c (IntersectionCirclesPoint _ ?c _) => apply OnCircle2IntersectionCirclesPoint

	| |- OnCircle ?c (InterDiameterPoint _ ?c _) => apply OnCircleInterDiameterPoint
	| |- OnCircle ?c (SecondInterDiameterPoint _ ?c _) => apply OnCircleSecondInterDiameterPoint

	| |- OnCircle (Compass _ _ _) _ => simpl; solveDistance2
	| |- OnCircle ?c _ => unfold c; simpl; solveDistance2
end.

Ltac solveEq6 := match goal with
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

	| |- ?M = AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 => apply (UniqueAddSegmentPoint A B C D E H H0 M); [immEquiOriented5 | solveDistance2]
	| |- AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 = ?M => apply sym_eq; apply (UniqueAddSegmentPoint A B C D E H H0 M); [immEquiOriented5 | solveDistance2]

	| |- ?M = MarkSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueMarkSegmentPoint A B C D H M); [immClosedRay5 | solveDistance2]
	| |- MarkSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueMarkSegmentPoint A B C D H M); [immClosedRay5 | solveDistance2]

	| |- ?M = OppSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueOppSegmentPoint A B C D H M); [immSegment5 | solveDistance2]
	| |- OppSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueOppSegmentPoint A B C D H M); [immSegment5 | solveDistance2]

	| |- ?M = SymmetricPoint ?A ?B ?H => apply (UniqueSymmetricPoint A B H M); [immBetween5 | solveDistance2]
	| |- SymmetricPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueSymmetricPoint A B H M); [immBetween5 | solveDistance2]

	| H1 : IsAngle ?alpha, H2 : IsAngle ?beta |- ?alpha = ?beta => apply (EqAngle alpha beta H1 H2); solveDistance6

	| |- ?A = ?B => match type of A with
			| Point => let H := fresh in (assert (H : Distance A B = Oo); [solveDistance2 | apply (NullDistanceEq A B H)])
			end

	| |- ?X = _ => unfold X; solveEq5
	| |- _ = ?Y => unfold Y; solveEq5
end.

Ltac immCongruentAngle6 := match goal with 
	| |- CongruentAngle ?A ?B ?C ?A ?B ?C => apply (CongruentAngleRefl A B C); try immDistinct6
	| |- CongruentAngle ?A ?B ?C ?C ?B ?A => apply (CongruentAnglePerm A B C);  try immDistinct6

	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- CongruentAngle ?D ?E ?F ?A ?B ?C => apply (CongruentAngleSym A B C D E F H)
	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- CongruentAngle ?C ?B ?A ?D ?E ?F => apply (CongruentAngleRev1 A B C D E F H)
	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- CongruentAngle ?A ?B ?C ?F ?E ?D => apply (CongruentAngleRev2 A B C D E F H)
	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- CongruentAngle ?C ?B ?A ?F ?E ?D => apply (CongruentAngleRev A B C D E F H)

	|H : Angle ?A ?B ?C ?H1 ?H2  = Angle ?D ?E ?F ?H3 ?H4  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (CongruentEqAngle A B C D E F H1 H2 H3 H4 H)

	| H : OpenRay ?B ?A ?D |- CongruentAngle ?A ?B ?C ?D ?B ?C => apply (CongruentAngleSide1 A B C D); immediate5
	| H : OpenRay ?B ?C ?D |- CongruentAngle ?A ?B ?C ?A ?B ?D => apply (CongruentAngleSide2 A B C D); immediate5
	| H1 : OpenRay ?B ?A ?D, H2 : OpenRay ?B ?C ?E |- CongruentAngle ?A ?B ?C ?D ?B ?E => apply (CongruentAngleSides A B C D E); immediate5

end.

Ltac immNullAngle6 := match goal with 
	| H : NullAngle ?A ?B ?C |- NullAngle ?A ?B ?C => exact H
	| H : NullAngle ?A ?B ?C |- NullAngle ?C ?B ?A => apply (CongruentNullAngle A B C C B A); [exact H | apply CongruentAnglePerm; immDistinct6]

	| |- NullAngle ?A ?B ?C => apply (OpenRayNullAngle B A C); [immDistinct6 | immOpenRay6]

end.

Ltac immElongatedAngle6 := match goal with 
	| H : ElongatedAngle ?A ?B ?C |- ElongatedAngle ?A ?B ?C => exact H
	| H : ElongatedAngle ?A ?B ?C |- ElongatedAngle ?C ?B ?A => apply (CongruentElongatedAngle A B C C B A); [exact H | apply CongruentAnglePerm; immDistinct6]

	| |- ElongatedAngle ?A ?B ?C => apply (BetweenElongatedAngle B A C);  immBetween6

end.

Ltac immNotNullAngle6 := match goal with 
	| H : ElongatedAngle ?A ?B ?C |- ~NullAngle ?A ?B ?C => apply (ElongatedAngleNotNullAngle A B C H)
	| H : ElongatedAngle ?A ?B ?C |- ~NullAngle ?C ?B ?A => apply (ElongatedAngleNotNullAngle C B A); immElongatedAngle6
end.

Ltac immNotElongatedAngle6 := match goal with 
	| H : NullAngle ?A ?B ?C |- ~ElongatedAngle ?A ?B ?C => apply (NullAngleNotElongatedAngle A B C H)
	| H : NullAngle ?A ?B ?C |- ~ElongatedAngle ?C ?B ?A => apply (NullAngleNotElongatedAngle C B A); immNullAngle6
end.

Ltac solveAngle6 := match goal with 
	| |- Angle _ _ _ _ _ = Angle _ _ _ _ _ => apply EqCongruentAngle; immCongruentAngle6

	| |- Angle ?A ?B ?C _ _ = Uu => eqToCongruent6; immNullAngle6
	| |- Uu = Angle ?A ?B ?C _ _ => eqToCongruent6; immNullAngle6

	| |- Angle ?A ?B ?C _ _ = uU => eqToCongruent6; immElongatedAngle6
	| |- uU = Angle ?A ?B ?C _ _ => eqToCongruent6; immElongatedAngle6

	| |- Angle Uu Oo ?M _ _ = ?M => apply EqAnglePoint; immIsAngle6
	| |- ?M = Angle Uu Oo ?M _ _  => apply sym_eq; apply EqAnglePoint; immIsAngle6
	| |- Angle ?M Oo Uu ?H1 ?H2 = ?M => rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2));  apply EqAnglePoint; immIsAngle6
	| |- ?M = Angle ?M Oo Uu ?H1 ?H2  => apply sym_eq;  rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2)); apply EqAnglePoint; immIsAngle6

end.

Ltac immediate6 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate6
	| |- ?A \/ ?B => (left; immediate6)  || (right; immediate6)

	| |- DistancePlus _ _ = _ => solveDistance6
	| |- _ = DistancePlus _ _ => solveDistance6

	| |- DistanceTimes _ _ _ = _ => solveDistance6
	| |- _ = DistanceTimes _ _ _ => solveDistance6

	| |- Distance _ _ = _ => solveDistance6
	| |- _ = Distance _ _ => solveDistance6

	| |- IsDistance ?d => immIsDistance2 d

	| |- Angle _ _ _ _ _ = _ => solveAngle6
	| |-  _ = Angle _ _ _ _ _ => solveAngle6

	| |- CongruentAngle _ _ _ _ _ _ => immCongruentAngle6
	| |- NullAngle _ _ _ => immNullAngle6
	| |- ElongatedAngle _ _ _ => immElongatedAngle6
	| |- ~NullAngle _ _ _ => immNotNullAngle6
	| |- ~ElongatedAngle _ _ _ => immNotElongatedAngle6

	| |- IsAngle _ => immIsAngle6

	| |- _ = _ => solveEq6
	| |- _ <> _ => immDistinct6
	| |- ?A = ?B -> False => fold(A <> B); immDistinct6

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
end.

Ltac stepEq6 X Y H  := match type of H with
	| Point => apply trans_eq with (y:=H); unfold H; byDefEqPoint5

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

	| Angle ?C ?A ?B ?Hac ?Hab = Angle ?D ?A ?B ?Had ?Hab => eqToCongruent6; apply (EqAngleUniquePointSide1 A B C D); try immediate6
	| Angle ?B ?A ?C ?Hab ?Hac = Angle ?B ?A ?D ?Hab ?Had =>  eqToCongruent6; apply (EqAngleUniquePointSide2 A B C D); try immediate6

	| CongruentAngle ?C ?A ?B ?D ?A ?B =>  apply (EqAngleUniquePointSide1 A B C D H); try immediate6
	| CongruentAngle ?B ?A ?C ?B ?A ?D  => apply (EqAngleUniquePointSide2 A B C D H); try immediate6

	| IsAngle X => apply EqAngle; try immediate6
	| IsAngle Y => apply EqAngle; try immediate6

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

Ltac stepOpenRay6 A B C H := match type of H with

	| OpenRay A C B => apply OpenRaySym; [try immDistinct1 | exact H]
	| EquiOriented A C A B => apply OpenRaySym; [try immDistinct1 | apply H]
	| ClosedRay A B C => apply OpenRaySym; [try immDistinct1 | apply H]
	| OpenRay A B ?D => apply (OpenRayTrans A B D C) ; try immOpenRay1
	| EquiOriented A B A ?D => apply (OpenRayTrans A B D C) ; try immOpenRay1
	| ClosedRay A ?D B => apply (OpenRayTrans A B D C) ; try immOpenRay1
	| OpenRay A ?D C => apply (OpenRayTrans A B D C) ; try immOpenRay1
	| EquiOriented A ?D A C => apply (OpenRayTrans A B D C) ; try immOpenRay1
	| ClosedRay A C ?D => apply (OpenRayTrans A B D C) ; try immOpenRay1
	| EquiOriented ?D B A C => apply ClosedRayOpenRay; apply (EquiOrientedClosedRayClosedRay A C D B H); try immClosedRay1

	| Segment A C B => apply SegmentOpenRayAC; exact H
	| Segment C A B => apply SegmentOpenRayAC; apply (SegmentSym _ _ _ H)
	| Segment A B C => apply SegmentOpenRayAB; try immediate1
	| Segment B A C => apply SegmentOpenRayAB; try immediate1

	| Angle ?C ?A ?B ?Hac ?Hab = Angle ?D ?A ?B ?Had ?Hab => eqToCongruent6; apply (EqAngleOpenRay1 A B C D); try immediate6
	| Angle ?B ?A ?C ?Hab ?Hac = Angle ?B ?A ?D ?Hab ?Had => eqToCongruent6; apply (EqAngleOpenRay2 A B C D); try immediate6

	| CongruentAngle ?C ?A ?B ?D ?A ?B => apply (EqAngleOpenRay1 A B C D); try immediate6
	| CongruentAngle ?B ?A ?C ?B ?A ?D => apply (EqAngleOpenRay2 A B C D); try immediate6

	| Point => match H with
		| Uu => apply NullAngleOpenRay
		end

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate6
end.

Ltac stepBetween6 A B D H := match type of H with

	| Segment A D B => apply SegmentBetween; try immediate6
	| Segment D A B => apply BetweenSym; apply SegmentBetween; try immediate6

	| OpenRay B ?C D => apply (OpenRayBetween A B C D H); try immediate6
	| ClosedRay B D ?C => apply (OpenRayBetween A B C D); try immediate6
	| OpenRay B D ?C => apply (OpenRayBetween A B C D H); try immediate6
	| ClosedRay B ?C D => apply (OpenRayBetween A B C D); try immediate6
	| EquiOriented B ?C B D => apply (OpenRayBetween A B C D); try immediate6
	| OpenRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate6
	| ClosedRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate6
	| OpenRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate6
	| ClosedRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate6
	| EquiOriented B ?C B A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate6

	| Between A B ?C => apply (OpenRayBetween A B C D); try immediate6
	| Between ?C B A => apply (OpenRayBetween A B C D); try immediate6
	| Between D B ?C => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate6
	| Between ?C B D => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate6
	| Segment A ?C B => apply (OpenRayBetween A B C D); try immediate3
	| Segment ?C A B => apply (OpenRayBetween A B C D); try immediate3
	| Segment D ?C B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3
	| Segment ?C D B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate3

	| Between ?E B ?F => apply (OpenRaysBetween B E F A D H); try immediate3

	| Point => match H with
		| uU => apply ElongatedAngleBetween
		end

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate6
end.

Ltac stepCongruentTransAngle6 A B C D E F H := match type of H with
		| CongruentAngle A B C ?X ?Y ?Z => apply (CongruentAngleTrans A B C X Y Z D E F H);  try immediate6
		| CongruentAngle C B A ?X ?Y ?Z => apply CongruentAngleRev1;  apply (CongruentAngleTrans C B A X Y Z D E F H);  try immediate6
		| CongruentAngle ?X ?Y ?Z  A B C => apply (CongruentAngleTrans  A B C X Y Z D E F (CongruentAngleSym X Y Z A B C H));  try immediate6
		| CongruentAngle ?X ?Y ?Z  C B A =>  apply CongruentAngleRev1; apply (CongruentAngleTrans  C B A X Y Z D E F (CongruentAngleSym X Y Z C B A H));  try immediate6
		
		| CongruentAngle D E F ?X ?Y ?Z => apply CongruentAngleSym; apply (CongruentAngleTrans D E F X Y Z A B C H);  try immediate6
		| CongruentAngle F E D ?X ?Y ?Z => apply CongruentAngleSym; apply CongruentAngleRev1;  apply (CongruentAngleTrans F E D X Y Z A B C H);  try immediate6
		| CongruentAngle ?X ?Y ?Z  D E F => apply CongruentAngleSym; apply (CongruentAngleTrans D E F X Y Z A B C (CongruentAngleSym X Y Z D E F H));  try immediate6
		| CongruentAngle ?X ?Y ?Z  F E D =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (CongruentAngleTrans F E D X Y Z A B C (CongruentAngleSym X Y Z F E D H));  try immediate6
end.

Ltac stepCongruentAngle6 A B C D E F H :=  match type of H with
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

	| ?X = ?Y => rewrite H || rewrite <- H

	
	| _ => eqToCongruent6; try immediate6
end.

Ltac stepNullAngle6 A B C H :=  match type of H with
	| _ <> _  => apply (OpenRayNullAngle B A C);  try immediate6
	| OpenRay _ _ _  => apply (OpenRayNullAngle B A C);  try immediate6
	| ClosedRay _ _ _  => apply (OpenRayNullAngle B A C);  try immediate6

	| NullAngle ?D ?E ?F => apply (CongruentNullAngle D E F A B C H); try immediate6

	| CongruentAngle ?D ?E ?F A B C => apply (CongruentNullAngle D E F A B C); try immediate6
	| CongruentAngle ?D ?E ?F C B A => apply (CongruentNullAngle D E F A B C); try immediate6
	| CongruentAngle A B C ?D ?E ?F => apply (CongruentNullAngle D E F A B C); try immediate6
	| CongruentAngle C B A ?D ?E ?F => apply (CongruentNullAngle D E F A B C); try immediate6
end.

Ltac stepElongatedAngle6 A B C H :=  match type of H with
	| ElongatedAngle ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C H); try immediate6

	| CongruentAngle ?D ?E ?F A B C => apply (CongruentElongatedAngle D E F A B C); try immediate6
	| CongruentAngle ?D ?E ?F C B A => apply (CongruentElongatedAngle D E F A B C); try immediate6
	| CongruentAngle A B C ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C); try immediate6
	| CongruentAngle C B A ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C); try immediate6

	| Segment A C B => apply BetweenElongatedAngle; try immediate6
	| Segment C A B => apply BetweenElongatedAngle; try immediate6
end.

Ltac stepCollinear6 H := match type of H with

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

	| CongruentAngle ?A ?B ?C ?D ?E ?F => match goal with
		| |- Collinear D E F => apply (CongruentAngleCollinear A B C D E F); try immediate6
		| |- Collinear D F E => apply CollinearACB; apply (CongruentAngleCollinear A B C D E F); try immediate6
		| |- Collinear E D F => apply CollinearBAC; apply (CongruentAngleCollinear A B C D E F); try immediate6
		| |- Collinear E F D => apply CollinearBCA; apply (CongruentAngleCollinear A B C D E F); try immediate6
		| |- Collinear F D E => apply CollinearCAB; apply (CongruentAngleCollinear A B C D E F); try immediate6
		| |- Collinear F E D => apply CollinearCBA; apply (CongruentAngleCollinear A B C D E F); try immediate6

		| |- Collinear A B C => apply (CongruentAngleCollinear D E F A B C); try immediate6
		| |- Collinear A C B => apply CollinearACB; apply (CongruentAngleCollinear D E F A B C); try immediate6
		| |- Collinear B A C => apply CollinearBAC; apply (CongruentAngleCollinear D E F A B C); try immediate6
		| |- Collinear B C A => apply CollinearBCA; apply (CongruentAngleCollinear D E F A B C); try immediate6
		| |- Collinear C A B => apply CollinearCAB; apply (CongruentAngleCollinear D E F A B C); try immediate6
		| |- Collinear C B A => apply CollinearCBA; apply (CongruentAngleCollinear D E F A B C); try immediate6
		end

	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate3
end.

Ltac step6 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance2 H
	| |- _ = DistancePlus _ _  => stepEqDistance2 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance2 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance2 H
	| |- Distance _ _ = _ => stepEqDistance2 H
	| |- _ = Distance _ _ => stepEqDistance2 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |- _ = H => try unfold H; byDefEqPoint5
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint5

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent6; try immediate6
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent6; try immediate6

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle6 A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle6 A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle6 A B C H

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
end.

Ltac since6 txt := assert txt; try immediate6.

Ltac from6 H txt := assert txt; [(step6 H ; try immediate6) |  try immediate6].

Ltac as6 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate6 | (step6 Hyp ; try immediate6)]).
