
Ltac immClockwise11 := match goal with
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

	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?A ?B ?C => apply (StrictParallelogrammClockwiseABC A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?B ?C ?A => apply ClockwiseBCA;apply (StrictParallelogrammClockwiseABC A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?C ?A ?B => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseABC A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?B ?C ?D => apply (StrictParallelogrammClockwiseBCD A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?C ?D ?B => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseBCD A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?D ?B ?C => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseBCD A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?C ?D ?A => apply (StrictParallelogrammClockwiseCDA A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?D ?A ?C => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseCDA A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?A ?C ?D => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseCDA A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?D ?A ?B => apply (StrictParallelogrammClockwiseDAB A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?A ?B ?D => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseDAB A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- Clockwise ?B ?D ?A => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseDAB A B C D H)


	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?A ?B (SPCenter ?A ?B ?C ?D ?H) => apply (StrictParallelogrammClockwiseABK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?B (SPCenter ?A ?B ?C ?D ?H) ?A => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseABK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise (SPCenter ?A ?B ?C ?D ?H) ?A ?B => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseABK A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?B ?C (SPCenter ?A ?B ?C ?D ?H) => apply (StrictParallelogrammClockwiseBCK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?C (SPCenter ?A ?B ?C ?D ?H) ?B => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseBCK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise (SPCenter ?A ?B ?C ?D ?H) ?B ?C => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseBCK A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?C ?D (SPCenter ?A ?B ?C ?D ?H) => apply (StrictParallelogrammClockwiseCDK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?D (SPCenter ?A ?B ?C ?D ?H) ?C => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseCDK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise (SPCenter ?A ?B ?C ?D ?H) ?C ?D => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseCDK A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?D ?A (SPCenter ?A ?B ?C ?D ?H) => apply (StrictParallelogrammClockwiseDAK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise ?A (SPCenter ?A ?B ?C ?D ?H) ?D => apply ClockwiseBCA; apply (StrictParallelogrammClockwiseDAK A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D  |- Clockwise (SPCenter ?A ?B ?C ?D ?H) ?D ?A => apply ClockwiseCAB; apply (StrictParallelogrammClockwiseDAK A B C D H)
end.

Ltac immNotClockwise11 := match goal with
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
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?B ?C ?A => intro; elim H; immClockwise11
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?C ?A ?B => intro; elim H; immClockwise11

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?D => apply (EquiOrientedNotClockwiseABD _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?D ?A => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise11
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?D ?A ?B => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise11

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?C => apply (EquiOrientedNotClockwiseABC _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?C ?A => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise11
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?C ?A ?B => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise11

	|  |- ~Clockwise ?A ?B ?C => apply ClockwiseNotClockwise; immClockwise11
	|  |- ~Clockwise ?A ?B ?C => apply CollinearNotClockwise; immCollinear9 
end.

Ltac immDistinct11 := match goal with
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

	| H : StrictParallelogramm ?A ?B ?C ?D |- ?A <> ?B => apply (StrictParallelogrammDistinctAB A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?B <> ?A => apply sym_not_eq; apply (StrictParallelogrammDistinctAB A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D |- ?B <> ?C => apply (StrictParallelogrammDistinctBC A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?C <> ?B => apply sym_not_eq; apply (StrictParallelogrammDistinctBC A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D |- ?C <> ?D => apply (StrictParallelogrammDistinctCD A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?D <> ?C => apply sym_not_eq; apply (StrictParallelogrammDistinctCD A B C D H)

	| H : StrictParallelogramm ?A ?B ?C ?D |- ?D <> ?A => apply (StrictParallelogrammDistinctDA A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?A <> ?D => apply sym_not_eq; apply (StrictParallelogrammDistinctDA A B C D H)

	| Hp : Parallelogramm ?A ?B ?C ?D, Hab : ?A <> ?B |- ?C <> ?D => apply (ParallelogrammDistinctABDistinctCD A B C D Hp Hab)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hab : ?A <> ?B |- ?D <> ?C => apply sym_not_eq; apply (ParallelogrammDistinctABDistinctCD A B C D Hp Hab)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hba : ?B <> ?A |- ?C <> ?D => apply (ParallelogrammDistinctABDistinctCD A B C D Hp (sym_not_eq Hba))
	| Hp : Parallelogramm ?A ?B ?C ?D, Hba : ?B <> ?A |- ?D <> ?C => apply sym_not_eq; apply (ParallelogrammDistinctABDistinctCD A B C D Hp  (sym_not_eq Hba))

	| Hp : Parallelogramm ?A ?B ?C ?D, Hbc : ?B <> ?C |- ?D <> ?A => apply (ParallelogrammDistinctBCDistinctDA A B C D Hp Hbc)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hbc : ?B <> ?C |- ?A <> ?D => apply sym_not_eq; apply (ParallelogrammDistinctBCDistinctDA A B C D Hp Hbc)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hcb : ?C <> ?B |- ?D <> ?A => apply (ParallelogrammDistinctBCDistinctDA A B C D Hp (sym_not_eq Hcb))
	| Hp : Parallelogramm ?A ?B ?C ?D, Hcb : ?C <> ?B |- ?A <> ?D => apply sym_not_eq; apply (ParallelogrammDistinctBCDistinctDA A B C D Hp  (sym_not_eq Hcb))

	| Hp : Parallelogramm ?A ?B ?C ?D, Hcd : ?C <> ?D |- ?A <> ?B => apply (ParallelogrammDistinctCDDistinctAB A B C D Hp Hcd)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hcd : ?C <> ?D |- ?B <> ?A => apply sym_not_eq; apply (ParallelogrammDistinctCDDistinctAB A B C D Hp Hcd)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hdc : ?D <> ?C |- ?A <> ?B => apply (ParallelogrammDistinctCDDistinctAB A B C D Hp (sym_not_eq Hdc))
	| Hp : Parallelogramm ?A ?B ?C ?D, Hdc : ?D <> ?C |- ?B <> ?A => apply sym_not_eq; apply (ParallelogrammDistinctCDDistinctAB A B C D Hp  (sym_not_eq Hdc))

	| Hp : Parallelogramm ?A ?B ?C ?D, Hda : ?D <> ?A |- ?B <> ?C => apply (ParallelogrammDistinctDADistinctBC A B C D Hp Hda)
	| Hp : Parallelogramm ?A ?B ?C ?D, Hda : ?D <> ?A |- ?C <> ?B => apply sym_not_eq; apply (ParallelogrammDistinctDADistinctBC A B C D Hp Hda)
	| Hp : Parallelogramm ?A ?B ?C ?D, Had : ?A <> ?D |- ?B <> ?C => apply (ParallelogrammDistinctDADistinctBC A B C D Hp (sym_not_eq Had))
	| Hp : Parallelogramm ?A ?B ?C ?D, Had : ?A <> ?D |- ?C <> ?B => apply sym_not_eq; apply (ParallelogrammDistinctDADistinctBC A B C D Hp  (sym_not_eq Had))

	| H : Parallelogramm ?A ?B ?C ?D |- ?A <> ?C => inversion H; immDistinct1
	| H : Parallelogramm ?A ?B ?C ?D |- ?C <> ?A => inversion H; immDistinct1
	| H : Parallelogramm ?A ?B ?C ?D |- ?B <> ?D => inversion H; immDistinct1
	| H : Parallelogramm ?A ?B ?C ?D |- ?D <> ?B => inversion H; immDistinct1

	| H : StrictParallelogramm ?A ?B ?C ?D |- ?A <> ?C => inversion H; immDistinct1
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?C <> ?A => inversion H; immDistinct1
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?B <> ?D => inversion H; immDistinct1
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?D <> ?B => inversion H; immDistinct1
end.

Ltac immParallelogramm11 := match goal with 
	|  |- Parallelogramm ?A ?B ?C (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) => apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm ?A (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) ?C ?B => apply ParallelogrammRev; apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) ?A ?B ?C => do 3 apply ParallelogrammPerm; apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) ?C ?B ?A => apply ParallelogrammRev; do 3 apply ParallelogrammPerm; apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm ?C (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) ?A ?B => do 2 apply ParallelogrammPerm; apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm ?C ?B ?A (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) => apply ParallelogrammRev; do 2 apply ParallelogrammPerm; apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm ?B ?C (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) ?A => apply ParallelogrammPerm; apply (ParallelogrammVertex4 A B C Hac Hbk)
	|  |- Parallelogramm ?B ?A (SymmetricPoint ?B (MidPoint ?A ?C ?Hac) ?Hbk) ?C => apply ParallelogrammRev; apply ParallelogrammPerm; apply (ParallelogrammVertex4 A B C Hac Hbk)

	| H : Parallelogramm ?A ?B ?C ?D |- Parallelogramm ?A ?B ?C ?D => exact H
	| H : Parallelogramm ?A ?D ?C ?B |- Parallelogramm ?A ?B ?C ?D => apply ParallelogrammRev; exact H
	| H : Parallelogramm ?D ?A ?B ?C |- Parallelogramm ?A ?B ?C ?D => apply ParallelogrammPerm; exact H
	| H : Parallelogramm ?D ?C ?B ?A |- Parallelogramm ?A ?B ?C ?D => apply ParallelogrammPerm; apply ParallelogrammRev; exact H
	| H : Parallelogramm ?C ?D ?A ?B |- Parallelogramm ?A ?B ?C ?D => do 2 apply ParallelogrammPerm; exact H
	| H : Parallelogramm ?C ?B ?A ?D |- Parallelogramm ?A ?B ?C ?D => do 2 apply ParallelogrammPerm; apply ParallelogrammRev; exact H
	| H : Parallelogramm ?B ?C ?D ?A |- Parallelogramm ?A ?B ?C ?D => do 3 apply ParallelogrammPerm; exact H
	| H : Parallelogramm ?B ?A ?D ?C |- Parallelogramm ?A ?B ?C ?D => do 3 apply ParallelogrammPerm; apply ParallelogrammRev; exact H

	| H : StrictParallelogramm ?A ?B ?C ?D |- Parallelogramm ?A ?B ?C ?D => let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?A ?D ?C ?B |- Parallelogramm ?A ?B ?C ?D => apply ParallelogrammRev; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?D ?A ?B ?C |- Parallelogramm ?A ?B ?C ?D => apply ParallelogrammPerm; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?D ?C ?B ?A |- Parallelogramm ?A ?B ?C ?D => apply ParallelogrammPerm; apply ParallelogrammRev; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?C ?D ?A ?B |- Parallelogramm ?A ?B ?C ?D => do 2 apply ParallelogrammPerm; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?C ?B ?A ?D |- Parallelogramm ?A ?B ?C ?D => do 2 apply ParallelogrammPerm; apply ParallelogrammRev; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?B ?C ?D ?A |- Parallelogramm ?A ?B ?C ?D => do 3 apply ParallelogrammPerm; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)
	| H : StrictParallelogramm ?B ?A ?D ?C |- Parallelogramm ?A ?B ?C ?D => do 3 apply ParallelogrammPerm; apply ParallelogrammRev; let Hyp := fresh in (inversion H as (Hyp,_); exact Hyp)

	| H : MidPoint ?A ?C ?Hac = MidPoint ?B ?D ?Hbd |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac Hbd H)
	| H : MidPoint ?C ?A ?Hca = MidPoint ?B ?D ?Hbd |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) Hbd); step10 H; immediate10
	| H : MidPoint ?A ?C ?Hac = MidPoint ?D ?B ?Hdb |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac (sym_not_eq Hdb)); step10 H; immediate10
	| H : MidPoint ?C ?A ?Hca = MidPoint ?D ?B ?Hdb |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) (sym_not_eq Hdb)); let Hyp := fresh in (assert (Hyp : MidPoint A C (sym_not_eq Hca) = MidPoint C A Hca); [immediate10 | step10 Hyp; step10 H; immediate10])

	| H : MidPoint ?B ?D ?Hbd = MidPoint ?A ?C ?Hac |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac Hbd (sym_eq H))
	| H : MidPoint ?B ?D ?Hbd = MidPoint ?C ?A ?Hca |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) Hbd); step10 H; immediate10
	| H : MidPoint ?D ?B ?Hdb = MidPoint ?A ?C ?Hac |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac (sym_not_eq Hdb)); step10 H; immediate10
	| H : MidPoint ?D ?B ?Hdb = MidPoint ?C ?A ?Hca |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) (sym_not_eq Hdb)); let Hyp := fresh in (assert (Hyp : MidPoint A C (sym_not_eq Hca) = MidPoint C A Hca); [immediate10 | step10 Hyp; step10 H; immediate10])
end.

Ltac immBetween11 :=  match goal with
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

	| |- Between ?A (PCenter ?A _ ?C _  _) ?C => apply PCenterBetweenAC
	| |- Between ?C (PCenter ?A _ ?C _  _) ?A => apply BetweenSym; apply PCenterBetweenAC
	| |- Between ?B (PCenter _ ?B _ ?D _) ?D => apply PCenterBetweenBD
	| |- Between ?D (PCenter _ ?B _ ?D _) ?B => apply BetweenSym; apply PCenterBetweenBD

	| |- Between ?A (SPCenter ?A _ ?C _  ?H) ?C => DestructSP11 H; apply PCenterBetweenAC
	| |- Between ?C (SPCenter ?A _ ?C _  ?H) ?A => DestructSP11 H; apply BetweenSym; apply PCenterBetweenAC
	| |- Between ?B (SPCenter _ ?B _ ?D ?H) ?D => DestructSP11 H; apply PCenterBetweenBD
	| |- Between ?D (SPCenter _ ?B _ ?D ?H) ?B => DestructSP11 H; apply BetweenSym; apply PCenterBetweenBD

	| |- Between ?B _ _ => unfold B; immBetween6
	| |- Between _ ?B _ => unfold B; immBetween6
	| |- Between _ _ ?B => unfold B; immBetween6
end.

Ltac immSegment11 := match goal with
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

	| |- Segment _ _ _  => apply BetweenSegment; immBetween11

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immTCongruent11 := match goal with
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
 		(assert (Hyp1 := (TCongruentMidLineAMidLineB A B Hab));
		assert (Hyp2 := (TCongruentAIA'BIA' A B Hab));
		assert (Hyp3 := (TCongruentAIB'BIB' A B Hab));
		assert (Hyp4 := (TCongruentAIA'AIB' A B Hab));
		assert (Hyp5 := (TCongruentBIA'BIB' A B Hab)));
		immTCongruent7

	| |- context [(PCenter ?A ?B ?C ?D ?Hp)] => let Hyp1 := fresh in let Hyp2 := fresh in  		(assert (Hyp1 := ParallelogrammTCongruentAKBCKD A B C D Hp);
		assert (Hyp2 := ParallelogrammTCongruentBKCDKA A B C D Hp));
		immTCongruent7

	| |- context [(SPCenter ?A ?B ?C ?D ?Hsp)] => DestructSP11 Hsp; match goal with 
		| |- context [(PCenter ?A ?B ?C ?D ?Hp)] => let Hyp1 := fresh in let Hyp2 := fresh in  			(assert (Hyp1 := ParallelogrammTCongruentAKBCKD A B C D Hp);
			assert (Hyp2 := ParallelogrammTCongruentBKCDKA A B C D Hp));
			immTCongruent7
		end

	| Hp : Parallelogramm ?A ?B ?C ?D |- _ => let Hyp1 := fresh in let Hyp2 := fresh in  		(assert (Hyp1 := ParallelogrammTCongruentABCCDA A B C D Hp);
		assert (Hyp2 := ParallelogrammTCongruentBCDDAB A B C D Hp));
		immTCongruent7

	| H : StrictParallelogramm ?A ?B ?C ?D |- _ => DestructSP11 H; match goal with 
		| Hp : Parallelogramm ?A ?B ?C ?D |- _ => let Hyp1 := fresh in let Hyp2 := fresh in  			(assert (Hyp1 := ParallelogrammTCongruentABCCDA A B C D Hp);
			assert (Hyp2 := ParallelogrammTCongruentBCDDAB A B C D Hp));
			immTCongruent7
		end	
	| _ => solve [usingSSS7; immediate8
				| usingSASa7; immediate8
				| usingSASb7; immediate8 
				| usingSASc7; immediate8
				| usingASAab7; immediate8 
				| usingASAbc7; immediate8
				| usingASAca7; immediate8]
	
end.

Ltac generalizeDistParallelogramm11 := repeat match goal with
	| H : Parallelogramm ?A ?B ?C ?D  |- _ => 
		generalize (ParallelogrammABeqCD A B C D H);
		generalize (ParallelogrammBCeqDA A B C D H);
		generalize H; clear H

	| H : StrictParallelogramm ?A ?B ?C ?D  |- _ => DestructSP11 H;
		generalize H; clear H
end.

Ltac solveDist11 :=try solveOnCircleDist2; try generalizeMid9; generalizeDistParallelogramm11 ; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2;  unfoldDistance2; solveEq2.

Ltac solveDistPlus11 := try generalizeMid9;  generalizeDistParallelogramm11 ; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistancePlus2; unfoldDistancePlus2; substDistancePlus2; solveEq2.

Ltac solveDistTimes11 := try generalizeMid9;  generalizeDistParallelogramm11 ; generalizeDistTCongruent7; generalizeDistIsosceles7; generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistanceTimes2; unfoldDistanceTimes2; substDistanceTimes2; solveEq2.

Ltac solveDistance11 := simplDistance10; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus11
	| |- _ = DistancePlus _ _ => solveDistPlus11

	| |- DistanceTimes _ _ _ = _ => solveDistTimes11
	| |- _ = DistanceTimes _ _ _ => solveDistTimes11

	| |- Distance _ _ = _ => solveDist11
	| |- _ = Distance _ _ => apply sym_eq; solveDist11

	| |- _ => solveEq9
end.

Ltac immStrictParallelogramm11 := match goal with 
	|  |- StrictParallelogramm ?A ?B ?C ?D  => apply SPDef; [immParallelogramm11 | immClockwise11]

	| H : StrictParallelogramm ?B ?C ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => do 3 apply StrictParallelogrammPerm; exact H
	| H : StrictParallelogramm ?C ?D ?A ?B |- StrictParallelogramm ?A ?B ?C ?D  => do 2 apply StrictParallelogrammPerm; exact H
	| H : StrictParallelogramm ?D ?A ?B ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply StrictParallelogrammPerm; exact H

	| H : Clockwise ?B ?C ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseBCDStrictParallelogramm;  [immParallelogramm11 | immClockwise1]
	| H : Clockwise ?C ?D ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseBCDStrictParallelogramm;  [immParallelogramm11 | immClockwise1]
	| H : Clockwise ?D ?B ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseBCDStrictParallelogramm;  [immParallelogramm11 | immClockwise1]

	| H : Clockwise ?A ?C ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseCDAStrictParallelogramm; [immParallelogramm11 | immClockwise1]
	| H : Clockwise ?C ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseCDAStrictParallelogramm; [immParallelogramm11 | immClockwise1]
	| H : Clockwise ?D ?A ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseCDAStrictParallelogramm; [immParallelogramm11 | immClockwise1]

	| H : Clockwise ?A ?B ?D |- StrictParallelogramm ?A ?B ?C ?D => apply ClockwiseDABStrictParallelogramm; [immParallelogramm11 | immClockwise1]
	| H : Clockwise ?B ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseDABStrictParallelogramm; [immParallelogramm11 | immClockwise1]
	| H : Clockwise ?D ?A ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseDABStrictParallelogramm; [immParallelogramm11 | immClockwise1]

	| H : Clockwise ?A ?B (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseABKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise ?B (PCenter ?A ?B ?C ?D ?Hp) ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseABKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?A ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseABKStrictParallelogramm A B C D Hp); immClockwise1

	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?B ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseBCKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise ?B ?C (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseBCKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise ?C (PCenter ?A ?B ?C ?D ?Hp) ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseBCKStrictParallelogramm A B C D Hp); immClockwise1

	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?C ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseCDKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise ?C ?D (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseCDKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise ?D (PCenter ?A ?B ?C ?D ?Hp) ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseCDKStrictParallelogramm A B C D Hp); immClockwise1

	| H : Clockwise ?A (PCenter ?A ?B ?C ?D ?Hp) ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseDAKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseDAKStrictParallelogramm A B C D Hp); immClockwise1
	| H : Clockwise ?D ?A (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseDAKStrictParallelogramm A B C D Hp); immClockwise1

	|  |- StrictParallelogramm ?A ?B ?C (StrictPVertex4 ?A ?B ?C ?H) => apply (StrictPVertex4Parallelogramm A B C H)
	|  |- StrictParallelogramm ?B ?C (StrictPVertex4 ?A ?B ?C ?H) ?A =>apply StrictParallelogrammPerm; apply (StrictPVertex4Parallelogramm A B C H)
	|  |- StrictParallelogramm ?C (StrictPVertex4 ?A ?B ?C ?H) ?A ?B => do 2 apply StrictParallelogrammPerm; apply (StrictPVertex4Parallelogramm A B C H)
	|  |- StrictParallelogramm (StrictPVertex4 ?A ?B ?C ?H) ?A ?B ?C => do 3 apply StrictParallelogrammPerm; apply (StrictPVertex4Parallelogramm A B C H)

end.

Ltac immEquiDirected11 := match goal with
	| H : EquiDirected ?A ?B ?C ?D |- EquiDirected ?A ?B ?C ?D => exact H
	| H : EquiDirected ?B ?A ?C ?D |- EquiDirected ?A ?B ?C ?D => apply EquiDirectedPermutAB; exact  H
	| H : EquiDirected ?A ?B ?D ?C |- EquiDirected ?A ?B ?C ?D => apply EquiDirectedPermutCD; exact  H
	| H : EquiDirected ?B ?A ?D ?C |- EquiDirected ?A ?B ?C ?D => apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; exact  H

	| H : EquiDirected ?A ?B ?C ?D |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; exact H
	| H : EquiDirected ?B ?A ?C ?D |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutAB; exact  H
	| H : EquiDirected ?A ?B ?D ?C |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutCD; exact  H
	| H : EquiDirected ?B ?A ?D ?C |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; exact  H

	| |-  EquiDirected ?A ?B ?C ?A   => apply CollinearEquiDirected; immCollinear1
	| |-  EquiDirected ?B ?A ?C ?A   => apply EquiDirectedPermutAB; apply CollinearEquiDirected; immCollinear1
	| |-  EquiDirected ?A ?B ?A  ?C  => apply EquiDirectedPermutCD; apply CollinearEquiDirected; immCollinear1
	| |-  EquiDirected ?B ?A ?A  ?C  => apply EquiDirectedSym; apply CollinearEquiDirected; immCollinear1

	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?A ?B ?C ?D => apply (ParallelogrammEquiDirected A B C D H)
	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?B ?A ?C ?D => apply EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D H)
	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?A ?B ?D ?C => apply EquiDirectedPermutCD; apply (ParallelogrammEquiDirected A B C D H)
	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?B ?A ?D ?C => apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D H)

	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply (ParallelogrammEquiDirected A B C D H)
	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?C ?D ?B ?A => apply EquiDirectedSym; apply EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D H)
	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?D ?C ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutCD; apply (ParallelogrammEquiDirected A B C D H)
	| H : Parallelogramm ?A ?B ?C ?D |-  EquiDirected ?D ?C ?B ?A => apply EquiDirectedSym; apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D H)

	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?A ?B ?C ?D => apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)
	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?B ?A ?C ?D => apply EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)
	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?A ?B ?D ?C => apply EquiDirectedPermutCD; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)
	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?B ?A ?D ?C => apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)

	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)
	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?C ?D ?B ?A => apply EquiDirectedSym; apply EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)
	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?D ?C ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutCD; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)
	| H : Parallelogramm ?D ?A ?B ?C |-  EquiDirected ?D ?C ?B ?A => apply EquiDirectedSym; apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; apply (ParallelogrammEquiDirected A B C D); apply (ParallelogrammPerm D A B C H)

	| Hp : StrictParallelogramm _ _ _ _ |-  EquiDirected ?A ?B ?C ?D => inversion_clear Hp; immEquiDirected11

end.

Ltac immEquiOriented11 := match goal with
	| |- EquiOriented ?A ?A ?B ?C => apply EquiOrientedAABC
	| |- EquiOriented ?A ?B ?A ?B => canonize1
	| H : EquiOriented ?A ?B ?C ?D |- EquiOriented ?A ?B ?C ?D => trivial
	| H : forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D M |- EquiOriented ?A ?B ?C ?D => trivial

	|  |- EquiOriented Oo (Distance _ _) Oo Uu => apply IsDistanceDistance
	|  |- EquiOriented  Oo Uu Oo (Distance _ _) => apply (ChangeAllABAC _ _ _); [apply IsDistanceDistance | try immDistinct1]
	|  |- EquiOriented  Uu Oo (Distance _ _) Oo => apply (ChangeSide _ _ _ _); [apply IsDistanceDistance | try immDistinct1]
	|  |- EquiOriented (Distance _ _) Oo Uu Oo => apply (ChangeSenseABAC _ _ _); apply IsDistanceDistance

	|  |- EquiOriented Oo (DistancePlus _ _) Oo Uu => apply IsDistanceDistancePlus
	|  |- EquiOriented  Oo Uu Oo (DistancePlus _ _) => apply (ChangeAllABAC _ _ _); [apply IsDistanceDistancePlus | try immDistinct1]
	|  |- EquiOriented  Uu Oo (DistancePlus _ _) Oo => apply (ChangeSide _ _ _ _); [apply IsDistanceDistancePlus | try immDistinct1]
	|  |- EquiOriented (DistancePlus _ _) Oo Uu Oo => apply (ChangeSenseABAC _ _ _); apply IsDistanceDistancePlus

	|  |- EquiOriented Oo (DistanceTimes _ _ _) Oo Uu => apply IsDistanceDistanceTimes
	|  |- EquiOriented  Oo Uu Oo (DistanceTimes _ _ _) => apply (ChangeAllABAC _ _ _); [apply IsDistanceDistanceTimes | try immDistinct1]
	|  |- EquiOriented  Uu Oo (DistanceTimes _ _ _) Oo => apply (ChangeSide _ _ _ _); [apply IsDistanceDistanceTimes | try immDistinct1]
	|  |- EquiOriented (DistanceTimes _ _ _) Oo Uu Oo => apply (ChangeSenseABAC _ _ _); apply IsDistanceDistanceTimes

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?C ?B ?A ?B => apply (ChangeAllABCB _ _ _ H); try immDistinct3
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?B ?C ?A ?B => apply (ChangeAllABBC _ _ _ H); try immDistinct3
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?C ?A ?A ?B => apply (ChangeAllABCA _ _ _ H); try immDistinct3
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented  ?A ?C ?A ?B => apply (ChangeAllABAC _ _ _ H); try immDistinct3

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?B ?C ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct3
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?C ?B ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct3
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?A ?C ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct3
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented  ?C ?A ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct3

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?B ?A ?B ?C => apply (ChangeSenseABCB _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?B ?A ?C ?B => apply (ChangeSenseABBC _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?B ?A ?A ?C => apply (ChangeSenseABCA _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented ?B ?A ?C ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : OpenRay ?A ?B ?C |- EquiOriented ?A ?B ?A ?C => exact H
	| H : OpenRay ?A ?B ?C |- EquiOriented  ?A ?C ?A ?B => apply (ChangeAllABAC _ _ _ H); try immDistinct3
	| H : OpenRay ?A ?B ?C |- EquiOriented  ?C ?A ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct3
	| H : OpenRay ?A ?B ?C |- EquiOriented ?B ?A ?C ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : ClosedRay ?A ?B ?C |- EquiOriented ?A ?C ?A ?B => exact H
	| H : ClosedRay ?A ?B ?C |- EquiOriented  ?A ?B ?A ?C => apply (ChangeAllABAC _ _ _ H); try immDistinct3
	| H : ClosedRay ?A ?B ?C |- EquiOriented  ?B ?A ?C ?A => apply (ChangeSide _ _ _ _ H); try immDistinct3
	| H : ClosedRay ?A ?B ?C |- EquiOriented ?C ?A ?B ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : Between ?A ?B ?C |- EquiOriented ?A ?B ?B ?C => destruct H; trivial
	| H : Between ?A ?B ?C |- EquiOriented ?B ?C ?A ?B => let Hyp1 := fresh in (let Hyp2 := fresh in (destruct H as (Hyp1,Hyp2); apply (ChangeAllABBC _ _ _ Hyp2 Hyp1)))
	| H : Between ?A ?B ?C |- EquiOriented ?C ?B ?B ?A => let Hyp1 := fresh in (let Hyp2 := fresh in (destruct H as (Hyp1,Hyp2); apply (ChangeSide _ _ _ _ Hyp2 Hyp1)))
	| H : Between ?A ?B ?C |- EquiOriented  ?B ?A ?C ?B => let Hyp := fresh in (destruct H as (_,Hyp); apply (ChangeSenseABBC _ _ _ Hyp))

	| H : Archimed ?A ?B ?C |- EquiOriented ?A ?C ?A ?B => apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- EquiOriented  ?A ?B ?A ?C => apply ChangeAllABAC; [apply (ArchimedianClosedRay _ _ _ H) |  try immDistinct3]
	| H : Archimed ?A ?B ?C |- EquiOriented  ?B ?A ?C ?A => apply ChangeSide; [apply (ArchimedianClosedRay _ _ _ H) |  try immDistinct3]
	| H : Archimed ?A ?B ?C |- EquiOriented ?C ?A ?B ?A => apply ChangeSenseABAC; apply (ArchimedianClosedRay _ _ _ H)

	| |- EquiOriented (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ _ _ => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2
	| |- EquiOriented _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2
	| |- EquiOriented _ _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2
	| |- EquiOriented _ _ _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2

	| |- EquiOriented (InterDiameterPoint ?l ?c ?H) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immEquiOriented4
	| |- EquiOriented _ (InterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immEquiOriented4
	| |- EquiOriented _ _ (InterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immEquiOriented4
	| |- EquiOriented _ _ _ (InterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle2; immEquiOriented4

	| |- EquiOriented (SecondInterDiameterPoint ?l ?c ?H) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immEquiOriented4
	| |- EquiOriented _ (SecondInterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immEquiOriented4
	| |- EquiOriented _ _ (SecondInterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immEquiOriented4
	| |- EquiOriented _ _ _ (SecondInterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle2; immEquiOriented4

	| |- EquiOriented (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOriented4
	| |- EquiOriented _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOriented4
	| |- EquiOriented _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOriented4
	| |- EquiOriented _ _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOriented4

	| |- EquiOriented (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOriented4
	| |- EquiOriented _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOriented4
	| |- EquiOriented _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOriented4
	| |- EquiOriented _ _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOriented4

	| |- EquiOriented (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOriented4
	| |- EquiOriented _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOriented4
	| |- EquiOriented _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOriented4
	| |- EquiOriented _ _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOriented4

	| |- EquiOriented (SymmetricPoint ?A ?B ?H) _ _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOriented4
	| |- EquiOriented _ (SymmetricPoint ?A ?B ?H) _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOriented4
	| |- EquiOriented _ _ (SymmetricPoint ?A ?B ?H) _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOriented4
	| |- EquiOriented _ _ _ (SymmetricPoint ?A ?B ?H) => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOriented4

	| |- EquiOriented (Graduation ?n ?A ?B ?Hab) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOriented2
	| |- EquiOriented _ (Graduation ?n ?A ?B ?Hab) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOriented2
	| |- EquiOriented _ _ (Graduation ?n ?A ?B ?Hab) _ => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOriented2
	| |- EquiOriented _ _ _ (Graduation ?n ?A ?B ?Hab) => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOriented2

	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?B ?A ?C ?D => apply (StrictParallelogrammEquiOriented A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?D ?C ?A ?B => apply (ChangeSide B A C D); [apply (StrictParallelogrammEquiOriented A B C D H) | apply (sym_not_eq (StrictParallelogrammDistinctAB A B C D H))]

	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?C ?B ?D ?A => apply (StrictParallelogrammEquiOriented B C D A (StrictParallelogrammPerm A B C D H))
	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?A ?D ?B ?C => apply (ChangeSide C B D A); [apply (StrictParallelogrammEquiOriented B C D A  (StrictParallelogrammPerm A B C D H)) | apply (sym_not_eq (StrictParallelogrammDistinctBC A B C D H))]

	| Hc : Collinear _  _ (PCenter ?A ?B ?C ?D ?H)  |- EquiOriented ?A ?B ?D ?C => apply (FlatParallelogramm A B C D H); immediate10
	| Hc : Collinear _  (PCenter ?A ?B ?C ?D ?H) _  |- EquiOriented ?A ?B ?D ?C => apply (FlatParallelogramm A B C D H); immediate10
	| Hc : Collinear  (PCenter ?A ?B ?C ?D ?H) _ _  |- EquiOriented ?A ?B ?D ?C => apply (FlatParallelogramm A B C D H); immediate10

	| |- EquiOriented ?A _ _ _ => unfold A; immEquiOriented4
	| |- EquiOriented _ ?A _ _ => unfold A; immEquiOriented4
	| |- EquiOriented _ _ ?A _ => unfold A; immEquiOriented4
	| |- EquiOriented _ _ _ ?A => unfold A; immEquiOriented4
end.

Ltac immCongruentAngle11 := match goal with 
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

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?B ?B ?C ?D  => apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?D ?B ?C ?D  => apply CongruentAngleRev1; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?B ?D ?C ?B  => apply CongruentAngleRev2; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?D ?D ?C ?B  => apply CongruentAngleRev; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?D ?D ?A ?B  => apply CongruentAngleSym; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?D ?B ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?B ?D ?A ?B  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?B ?B ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammDABeqBCD A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?C ?C ?D ?A  => apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?A ?C ?D ?A  => apply CongruentAngleRev1; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?C ?A ?D ?C  => apply CongruentAngleRev2; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?A ?A ?D ?C  => apply CongruentAngleRev; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?A ?A ?B ?C  => apply CongruentAngleSym; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?A ?C ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?C ?A ?B ?C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?C ?C ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammABCeqCDA A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?C ?D ?C ?A  => apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?B ?D ?C ?A  => apply CongruentAngleRev1; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?C ?A ?C ?D  => apply CongruentAngleRev2; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?B ?A ?C ?D  => apply CongruentAngleRev; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?A ?B ?A ?C  => apply CongruentAngleSym; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?A ?C ?A ?B  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?D ?B ?A ?C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?D ?C ?A ?B  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammBACeqDCA A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?C ?B ?C ?A  => apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?D ?B ?C ?A  => apply CongruentAngleRev1; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?C ?A ?C ?B  => apply CongruentAngleRev2; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?D ?A ?C ?B  => apply CongruentAngleRev; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?A ?D ?A ?C  => apply CongruentAngleSym; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?A ?C ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?B ?D ?A ?C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?B ?C ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammDACeqBCA A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?D ?C ?D ?B  => apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?A ?C ?D ?B  => apply CongruentAngleRev1; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?D ?B ?D ?C  => apply CongruentAngleRev2; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?A ?B ?D ?C  => apply CongruentAngleRev; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?B ?A ?B ?D  => apply CongruentAngleSym; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?B ?D ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?C ?A ?B ?D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?C ?D ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammABDeqCDB A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?B ?C ?B ?D  => apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?A ?C ?B ?D  => apply CongruentAngleRev1; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?B ?D ?B ?C  => apply CongruentAngleRev2; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?A ?D ?B ?C  => apply CongruentAngleRev; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?D ?A ?D ?B  => apply CongruentAngleSym; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?D ?B ?D ?A  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?C ?A ?D ?B  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?C ?B ?D ?A  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammADBeqCBD A B C D H); immDistinct11

	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?B ?B ?C ?D  => apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?D ?B ?C ?D  => apply CongruentAngleRev1; apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?B ?D ?C ?B  =>  apply CongruentAngleRev2; apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?D ?D ?C ?B  =>  apply CongruentAngleRev; apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?D ?D ?A ?B  =>  apply CongruentAngleSym; apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?D ?B ?A ?D  =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?B ?D ?A ?B  =>  apply CongruentAngleSym; apply CongruentAngleRev2; apply (StrictParallelogrammDABeqBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?B ?B ?A ?D  =>  apply CongruentAngleSym; apply CongruentAngleRev; apply (StrictParallelogrammDABeqBCD A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?C ?C ?D ?A  =>  apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?A ?C ?D ?A  =>  apply CongruentAngleRev1; apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?C ?A ?D ?C  =>  apply CongruentAngleRev2; apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?A ?A ?D ?C  =>  apply CongruentAngleRev; apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?A ?A ?B ?C  =>  apply CongruentAngleSym; apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?A ?C ?B ?A  =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?C ?A ?B ?C  =>  apply CongruentAngleSym; apply CongruentAngleRev2; apply (StrictParallelogrammABCeqCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?C ?C ?B ?A  =>  apply CongruentAngleSym; apply CongruentAngleRev; apply (StrictParallelogrammABCeqCDA A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?C ?D ?C ?A  =>  apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?B ?D ?C ?A  =>  apply CongruentAngleRev1; apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?C ?A ?C ?D  =>  apply CongruentAngleRev2; apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?B ?A ?C ?D  =>  apply CongruentAngleRev; apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?A ?B ?A ?C  =>  apply CongruentAngleSym; apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?A ?C ?A ?B  =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?D ?B ?A ?C  =>  apply CongruentAngleSym; apply CongruentAngleRev2; apply (StrictParallelogrammBACeqDCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?D ?C ?A ?B  =>  apply CongruentAngleSym; apply CongruentAngleRev; apply (StrictParallelogrammBACeqDCA A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?C ?B ?C ?A  =>  apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?D ?B ?C ?A  =>  apply CongruentAngleRev1; apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?C ?A ?C ?B  =>  apply CongruentAngleRev2; apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?D ?A ?C ?B  =>  apply CongruentAngleRev; apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?A ?D ?A ?C  =>  apply CongruentAngleSym; apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?A ?C ?A ?D  =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?B ?D ?A ?C  =>  apply CongruentAngleSym; apply CongruentAngleRev2; apply (StrictParallelogrammDACeqBCA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?B ?C ?A ?D  =>  apply CongruentAngleSym; apply CongruentAngleRev; apply (StrictParallelogrammDACeqBCA A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?D ?C ?D ?B  =>  apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?A ?C ?D ?B  =>  apply CongruentAngleRev1; apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?D ?B ?D ?C  =>  apply CongruentAngleRev2; apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?A ?B ?D ?C  =>  apply CongruentAngleRev; apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?B ?A ?B ?D  =>  apply CongruentAngleSym; apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?B ?D ?B ?A  =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?C ?A ?B ?D  =>  apply CongruentAngleSym; apply CongruentAngleRev2; apply (StrictParallelogrammABDeqCDB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?C ?D ?B ?A  =>  apply CongruentAngleSym; apply CongruentAngleRev; apply (StrictParallelogrammABDeqCDB A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?B ?C ?B ?D  =>  apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?A ?C ?B ?D  =>  apply CongruentAngleRev1; apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?B ?D ?B ?C  =>  apply CongruentAngleRev2; apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?A ?D ?B ?C  =>  apply CongruentAngleRev; apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?D ?A ?D ?B  =>  apply CongruentAngleSym; apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?D ?B ?D ?A  =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?C ?A ?D ?B  =>  apply CongruentAngleSym; apply CongruentAngleRev2; apply (StrictParallelogrammADBeqCBD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?C ?B ?D ?A  =>  apply CongruentAngleSym; apply CongruentAngleRev; apply (StrictParallelogrammADBeqCBD A B C D H) 

end.

Ltac immSupplement11 := match goal with
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

	| H : Parallelogramm ?A ?B ?C ?D  |- Supplement ?D ?A ?B ?A ?B ?C => apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?A ?B ?C =>  apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?C ?B ?A => apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?C ?B ?A =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?D ?A ?B => apply SupplementSym; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?B ?A ?D => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?D ?A ?B => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?B ?A ?D => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?B ?C ?D => apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?B ?C ?D =>  apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?D ?C ?B => apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?D ?C ?B =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?A ?B ?C => apply SupplementSym; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?C ?B ?A => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?A ?B ?C => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?C ?B ?A => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?C ?D ?A => apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?C ?D ?A =>  apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?A ?D ?C => apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?A ?D ?C =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?B ?C ?D => apply SupplementSym; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?D ?C ?B => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?B ?C ?D => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?D ?C ?B => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct11

	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?D ?A ?B => apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?D ?A ?B =>  apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?B ?A ?D => apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?B ?A ?D =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?C ?D ?A => apply SupplementSym; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?A ?D ?C => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?C ?D ?A => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?A ?D ?C => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct11

	| H : StrictParallelogramm ?A ?B ?C ?D  |- Supplement ?D ?A ?B ?A ?B ?C =>  apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?A ?B ?C =>    apply SupplementRev1;apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?C ?B ?A =>  apply SupplementRev2; apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?C ?B ?A =>    apply SupplementRev2; apply SupplementRev1;apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?D ?A ?B =>  apply SupplementSym; apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?B ?A ?D =>  apply SupplementSym; apply SupplementRev1; apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?D ?A ?B =>  apply SupplementSym; apply SupplementRev2; apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?B ?A ?D =>  apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (StrictParallelogrammDABSupplementAngleABC A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?B ?C ?D =>  apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?B ?C ?D =>    apply SupplementRev1;apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?D ?C ?B =>  apply SupplementRev2; apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?D ?C ?B =>    apply SupplementRev2; apply SupplementRev1;apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?A ?B ?C =>  apply SupplementSym; apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?C ?B ?A =>  apply SupplementSym; apply SupplementRev1; apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?A ?B ?C =>  apply SupplementSym; apply SupplementRev2; apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?C ?B ?A =>  apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (StrictParallelogrammABCSupplementAngleBCD A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?C ?D ?A =>  apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?C ?D ?A =>    apply SupplementRev1;apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?A ?D ?C =>  apply SupplementRev2; apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?A ?D ?C =>    apply SupplementRev2; apply SupplementRev1;apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?B ?C ?D =>  apply SupplementSym; apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?D ?C ?B =>  apply SupplementSym; apply SupplementRev1; apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?B ?C ?D =>  apply SupplementSym; apply SupplementRev2; apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?D ?C ?B =>  apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (StrictParallelogrammBCDSupplementAngleCDA A B C D H) 

	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?D ?A ?B =>  apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?D ?A ?B =>    apply SupplementRev1;apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?B ?A ?D =>  apply SupplementRev2; apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?B ?A ?D =>    apply SupplementRev2; apply SupplementRev1;apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?C ?D ?A =>  apply SupplementSym; apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?A ?D ?C =>  apply SupplementSym; apply SupplementRev1; apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?C ?D ?A =>  apply SupplementSym; apply SupplementRev2; apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 
	| H : StrictParallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?A ?D ?C =>   apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (StrictParallelogrammCDASupplementAngleDAB A B C D H) 

end.

Ltac immediate11 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate11
	| |- ?A \/ ?B => (left; immediate11)  || (right; immediate11)

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

	| |- _ = _ => solveEq9
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

	| |- TCongruent _ _ => immTCongruent11

	| |- Parallelogramm _ _ _ _ => immParallelogramm11
	| |- StrictParallelogramm _ _ _ _ => immStrictParallelogramm11
end.

Ltac stepSupplement11 A B C D E F H := match type of H with 
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

	| Parallelogramm ?X ?Y ?Z ?T  => match goal with
		| |- Supplement T X Y X Y Z => apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement Y X T X Y Z =>  apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement T X Y Z Y X => apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement Y X T Z Y X =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement X Y Z T X Y => apply SupplementSym; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement X Y Z Y X T => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement Z Y X T X Y => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11
		|  |- Supplement Z Y X Y X T => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate11

		|  |- Supplement X Y Z Y Z T => apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement Z Y X Y Z T =>  apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement X Y Z T Z Y => apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement Z Y X T Z Y =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement Y Z T X Y Z => apply SupplementSym; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement Y Z T Z Y X => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement T Z Y X Y Z => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11
		|  |- Supplement T Z Y Z Y X => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate11

		|  |- Supplement Y Z T Z T X => apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement T Z Y Z T X =>  apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement Y Z T X T Z => apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement T Z Y X T Z =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement Z T X Y Z T => apply SupplementSym; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement Z T X T Z Y => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement X T Z Y Z T => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11
		|  |- Supplement X T Z T Z Y => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate11

		|  |- Supplement Z T X T X Y => apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement X T Z T X Y =>  apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement Z T X Y X T => apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement X T Z Y X T =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement T X Y Z T X => apply SupplementSym; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement T X Y X T Z => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement Y X T Z T X => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
		|  |- Supplement Y X T X T Z => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate11
	end

end.

Ltac stepCongruentAngle11 A B C D E F H :=  match type of H with
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

	| Parallelogramm ?X ?Y ?Z ?T => match goal with
		| |- CongruentAngle T X Y Y Z T  => apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle Y X T Y Z T  => apply CongruentAngleRev1; apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle T X Y T Z Y  => apply CongruentAngleRev2; apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle Y X T T Z Y  => apply CongruentAngleRev; apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle Y Z T T X Y  => apply CongruentAngleSym; apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle Y Z T Y X T  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle T Z Y T X Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammDABeqBCD; try immediate11
		| |- CongruentAngle T Z Y Y X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammDABeqBCD; try immediate11

		| |- CongruentAngle X Y Z Z T X  => apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle Z Y X Z T X  => apply CongruentAngleRev1; apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle X Y Z X T Z  => apply CongruentAngleRev2; apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle Z Y X X T Z  => apply CongruentAngleRev; apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle Z T X X Y Z  => apply CongruentAngleSym; apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle Z T X Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle X T Z X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammABCeqCDA; try immediate11
		| |- CongruentAngle X T Z Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammABCeqCDA; try immediate11

		| |- CongruentAngle Y X Z T Z X  => apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle Z X Y T Z X  => apply CongruentAngleRev1; apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle Y X Z X Z T  => apply CongruentAngleRev2; apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle Z X Y X Z T  => apply CongruentAngleRev; apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle T Z X Y X Z  => apply CongruentAngleSym; apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle T Z X Z X Y  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle X Z T Y X Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammBACeqDCA; try immediate11
		| |- CongruentAngle X Z T Z X Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammBACeqDCA; try immediate11

		| |- CongruentAngle T X Z Y Z X  => apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle Z X T Y Z X  => apply CongruentAngleRev1; apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle T X Z X Z Y  => apply CongruentAngleRev2; apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle Z X T X Z Y  => apply CongruentAngleRev; apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle Y Z X T X Z  => apply CongruentAngleSym; apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle Y Z X Z X T  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle X Z Y T X Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammDACeqBCA; try immediate11
		| |- CongruentAngle Z Z Y Z X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammDACeqBCA; try immediate11

		| |- CongruentAngle X Y T Z T Y  => apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle T Y X Z T Y  => apply CongruentAngleRev1; apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle X Y T Y T Z  => apply CongruentAngleRev2; apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle T Y X Y T Z  => apply CongruentAngleRev; apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle Z T Y X Y T  => apply CongruentAngleSym; apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle Z T Y T Y X  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle Y T Z X Y T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammABDeqCDB; try immediate11
		| |- CongruentAngle Y T Z T Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammABDeqCDB; try immediate11

		| |- CongruentAngle X T Y Z Y T  => apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle Y T X Z Y T  => apply CongruentAngleRev1; apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle X T Y T Y Z  => apply CongruentAngleRev2; apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle Y T X T Y Z  => apply CongruentAngleRev; apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle Z Y T X T Y  => apply CongruentAngleSym; apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle Z Y T Y T X  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle T Y Z X T Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammADBeqCBD; try immediate11
		| |- CongruentAngle T Y Z Y T X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammADBeqCBD; try immediate11

		| |- CongruentAngle T X Y Z Y ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y X T Z Y ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T X Y ?U Y Z => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y X T ?U Y Z => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z Y ?U T X Y => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  Z Y ?U Y X T => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Y Z  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Y Z  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle X Y Z T Z ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z Y X T Z ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X Y Z ?U Z T => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z Y X ?U Z T => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T Z ?U X Y Z => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  T Z ?U Z Y X => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Z T  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Z T  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle Y Z T X T ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T Z Y X T ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y Z T ?U T X => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T Z Y ?U T X => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X T ?U Y Z T => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  X T ?U T Z Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U T X  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U T X  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle Z T X Y X ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X T Z Y X ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z T X ?U X Y => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X T Z ?U X Y => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y X ?U Z T X => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  Y X ?U X T Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U X Y  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U X Y  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle Y X T Z T ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T X Y Z T ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y X T ?U T Z => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T X Y ?U T Z => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z T ?U Y X T => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  Z T ?U T X Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U T Z  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U T Z  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle X T Z Y Z ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z T X Y Z ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X T Z ?U Z Y => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z T X ?U Z Y => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y Z ?U X T Z => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  Y Z ?U Z T X => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Z Y  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Z Y  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle T Z Y X Y ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y Z T X Y ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T Z Y ?U Y X => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Y Z T ?U Y X => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X Y ?U T Z Y => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  X Y ?U Y Z T => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Y X  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U Y X  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle Z Y X T X ?U => apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X Y Z T X ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle Z Y X ?U X T => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle X Y Z ?U X T => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle T X ?U Z Y X => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle  T X ?U X Y Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U X T  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate11
		| |- CongruentAngle ?U X T  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate11

		| |- CongruentAngle T X Y ?U Y X => apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle Y X T ?U Y X => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle T X Y X Y ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle Y X T X Y ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle ?U Y X T X Y => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle  ?U Y X Y X T => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle X Y ?U  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11
		| |- CongruentAngle X Y ?U  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate11

		| |- CongruentAngle Z T X ?U X T => apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle X T Z ?U X T => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle Z T X T X ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle X T Z T X ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle ?U X T Z T X => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle  ?U X T X T Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle T X ?U  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11
		| |- CongruentAngle T X ?U  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate11

		| |- CongruentAngle Y Z T ?U T Z => apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle T Z Y ?U T Z => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle Y Z T Z T ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle T Z Y Z T ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle ?U T Z Y Z T => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle  ?U T Z T Z Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle Z T ?U  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11
		| |- CongruentAngle Z T ?U  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate11

		| |- CongruentAngle X Y Z ?U Z Y => apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle Z Y X ?U Z Y => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle X Y Z Y Z ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle Z Y X Y Z ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle ?U Z Y X Y Z => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle  ?U Z Y Z Y X => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle Y Z ?U  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11
		| |- CongruentAngle Y Z ?U  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate11

		| |- CongruentAngle Y X T ?U T X => apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle T X Y ?U T X => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle Y X T X T ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle T X Y X T ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle ?U T X Y X T => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle  ?U T X T X Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle X T ?U  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11
		| |- CongruentAngle X T ?U  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate11

		| |- CongruentAngle Z Y X ?U X Y => apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle X Y Z ?U X Y => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle Z Y X Y X ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle X Y Z Y X ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle ?U X Y Z Y X => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle  ?U X Y X Y Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle Y X ?U  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11
		| |- CongruentAngle Y X ?U  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate11

		| |- CongruentAngle T Z Y ?U Y Z => apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle Y Z T ?U Y Z => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle T Z Y Z Y ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle Y Z T Z Y ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle ?U Y Z T Z Y => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle  ?U Y Z Y Z T => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle Z Y ?U  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11
		| |- CongruentAngle Z Y ?U  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate11

		| |- CongruentAngle X T Z ?U Z T => apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle Z T X ?U Z T => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle X T Z T Z ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle Z T X T Z ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle ?U Z T X T Z => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle  ?U Z T Z T X => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle T Z ?U  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11
		| |- CongruentAngle T Z ?U  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate11

	end

	| ?X = ?Y => rewrite H || rewrite <- H

	
	| _ => eqToCongruent6; try immediate8
end.

Ltac stepEquiOriented11 A B C D H := match type of H with

 	|  EquiOriented C D A B => apply (ChangeAll _ _ _ _ H); [try immDistinct1 | try ((left; immCollinear1) || (right; immCollinear1))]
 	|  EquiOriented D C B A => apply (ChangeSide _ _ _ _ H); try immDistinct1
 	|  EquiOriented B A D C => apply (ChangeSense _ _ _ _ H); try immCollinear1

 	|  EquiOriented A B ?E ?F => apply (EquiOrientedTrans A B E F C D H); try immEquiOriented1
 	|  EquiOriented B A ?F ?E => apply (EquiOrientedTrans A B E F C D); [stepEquiOriented1 A B E F H | try immEquiOriented1]
 	|  EquiOriented ?E ?F A B => apply (EquiOrientedTrans A B E F C D); [stepEquiOriented1 A B E F H  | try immEquiOriented1]
 	|  EquiOriented ?F ?E B A => apply (EquiOrientedTrans A B E F C D); [stepEquiOriented1 A B E F H  | try immEquiOriented1]

 	|  EquiOriented ?E ?F C D => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented1 | exact H]
	|  EquiOriented ?F ?E D C => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented1 | stepEquiOriented1 E F C D H]
 	|  EquiOriented C D ?E ?F => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented1 | stepEquiOriented1 E F C D H]
 	|  EquiOriented D C ?F ?E => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented1 | stepEquiOriented1 E F C D H]

	| OpenRay _ _ _ => unfold OpenRay in H; stepEquiOriented1 A B C D H
	| ClosedRay _ _ _ => unfold ClosedRay in H; stepEquiOriented1 A B C D H
	| Between ?E ?F ?G => let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in
					 (assert (Hyp1 := BetweenOpenRayAB E F G H); 
					 assert (Hyp2 := BetweenOpenRayAC E F G H); 
					 assert (Hyp3 := BetweenOpenRayCB E F G H));
					try immediate1
	| Segment ?E ?F ?G => let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in let Hyp4 := fresh in
					 (assert (Hyp1 := SegmentOpenRayAB E F G H); 
					 assert (Hyp2 := SegmentOpenRayAC E F G H); 
					 assert (Hyp3 := SegmentOpenRayAB F E G (SegmentSym _ _ _ H)); 
					 assert (Hyp4 := SegmentOpenRayAC F E G (SegmentSym _ _ _ H)));
					try immediate1
	| ?E <> ?F -> EquiOriented _  _ _ _ => let Hyp1 := fresh in let Hyp2 := fresh in
				(assert (Hyp1 : E <> F); [try immediate1  | assert (Hyp2 := H Hyp1);stepEquiOriented1 A B C D Hyp2])

	| Parallelogramm ?X ?Y ?Z ?T => first [
		let Hyp := fresh in (assert (Hyp : StrictParallelogramm X Y Z T H); [immediate11 | try immediate11]) |
		let Hyp := fresh in (assert (Hyp : Collinear X Y (PCenter X Y Z T H)); [immediate11 | try immediate11]) ]

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac stepStrictParallelogramm11 A B C D H := match type of H with
	|  Parallelogramm A B C D => apply (SPDef H);  try immediate11

	| Distance _ _ = Distance _ _ => apply EquiDistantStrictParallelogramm; try immediate11

	| Clockwise _ _ _ => apply EquiDistantStrictParallelogramm; try immediate11

	| CongruentAngle A B D B D C => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle D B A B D C => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle A B D C D B => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle D B A C D B => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle B D C A B D => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle B D C D B A => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle C D B A B D => apply CongruentAnglesParallelogramm;  try immediate11
	| CongruentAngle C D B D B A => apply CongruentAnglesParallelogramm;  try immediate11

	| Supplement A B C B C D => apply SupplementParallelogramm;  try immediate11
	| Supplement C B A B C D => apply SupplementParallelogramm;  try immediate11
	| Supplement A B C D C B => apply SupplementParallelogramm;  try immediate11
	| Supplement C B A D C B => apply SupplementParallelogramm;  try immediate11
	| Supplement B C D A B C => apply SupplementParallelogramm;  try immediate11
	| Supplement B C D C B A => apply SupplementParallelogramm;  try immediate11
	| Supplement D C B A B C => apply SupplementParallelogramm;  try immediate11
	| Supplement D C B C B A => apply SupplementParallelogramm;  try immediate11

end.

Ltac stepParallelogramm11 A B C D H := match type of H with
	| Point => unfold H; try immParallelogramm11

	| A <> C => match goal with
			| Hbd : B <> D |- _ => apply (Pllgm A B C D H Hbd); try immediate11
			| Hdb : D <> B |- _  => apply (Pllgm A B C D H (sym_not_eq Hdb)); try immediate11
			|  _ => let Hbd := fresh in (assert (Hbd : B <> D);
						[try immediate11 | apply (Pllgm A B C D H Hbd); try immediate11])
		end
	| C <> A => match goal with
			| Hbd : B <> D |- _  => apply (Pllgm A B C D (sym_not_eq H) Hbd); try immediate11
			| Hdb : D <> B |- _  => apply (Pllgm A B C D (sym_not_eq H) (sym_not_eq Hdb)); try immediate11 
			| _ => let Hbd := fresh in (assert (Hbd : B <> D);
						[try immediate11 | apply (Pllgm A B C D (sym_not_eq H) Hbd); try immediate11])
		end
	| B <> D => match goal with
			| Hac : A <> C |- _  => apply (Pllgm A B C D Hac H); try immediate11
			| Hca : C <> A |- _  => apply (Pllgm A B C D (sym_not_eq Hca)); try immediate11
			| _ => let Hac := fresh in (assert (Hac : A <> C);
						[try immediate11 | apply (Pllgm A B C D H Hac); try immediate11])
		end
	| D <> B => match goal with
			| Hac : A <> C |- _  => apply (Pllgm A B C D Hac (sym_not_eq H)); try immediate11
			| Hca : C <> A |- _  => apply (Pllgm A B C D (sym_not_eq Hca) (sym_not_eq H)); try immediate11
			| _ => let Hac := fresh in (assert (Hac : A <> C);
						[try immediate11 | apply (Pllgm A B C D Hac (sym_not_eq H)); try immediate11])
		end

	| Distance _ _ = Distance _ _ => first [
		 assert (Clockwise A B C); [immediate11 | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm11 A B C D H | immediate11]] |
		 assert (Clockwise B C D); [immediate11 | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm11 A B C D H | immediate11]] |
		 assert (Clockwise C D A); [immediate11 | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm11 A B C D H | immediate11]] |
		 assert (Clockwise D A B); [immediate11 | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm11 A B C D H | immediate11]] |

		 assert (Clockwise A C B); [immediate11 | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm11 A D C B H | immediate11]] |
		 assert (Clockwise B D C); [immediate11 | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm11 A D C B H | immediate11]] |
		 assert (Clockwise C A D); [immediate11 | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm11 A D C B H | immediate11]] |
		 assert (Clockwise D B A); [immediate11 | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm11 A D C B H | immediate11]] ]

end.

Ltac byDefEqPoint11 := match goal with
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

	| |- ?M = PCenter ?A ?B ?C ?D ?H => apply (UniquePCenter A B C D M H); first [right; split; immediate10 | left; split; immediate10 | idtac]
	| |- PCenter ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniquePCenter A B C D M H); first [right; split; immediate10 | left; split; immediate10 | idtac]

	| |- ?M = SPCenter ?A ?B ?C ?D ?H => apply (UniqueSPCenter A B C D M H); first [right; split; immediate10 | left; split; immediate10 | idtac]
	| |- SPCenter ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueSPCenter A B C D M H); first [right; split; immediate10 | left; split; immediate10 | idtac]

	| |- ?M = StrictPVertex4 ?A ?B ?C ?H => apply (UniqueStrictPVertex4 A B C M H); try immStrictParallelogramm11
	| |- StrictPVertex4 ?A ?B ?C ?H = ?M => apply sym_eq; apply (UniqueStrictPVertex4 A B C M H); try immStrictParallelogramm11
end.

Ltac step11 H := match goal with
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
	| |- RightAngle ?A ?B ?C => stepRightAngle10 A B C H

	| |- _ = H => unfold H; byDefEqPoint11
	| |- H = _ => apply sym_eq; unfold H; byDefEqPoint11

	| |- ?A = ?B => stepEq10 A B H
	| |- ?A <> ?B => stepDistinct3 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct3 A B H

	| |- Collinear _ _ _  => stepCollinear6 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented11 A B C D H
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

	| |- Parallelogramm ?A ?B ?C ?D => stepParallelogramm11 A B C D H
	| |- StrictParallelogramm ?A ?B ?C ?D => stepStrictParallelogramm11 A B C D H

end.

Ltac since11 txt := assert txt; try immediate11.

Ltac from11 H txt := assert txt; [(step11 H ; try immediate11) |  try immediate11].

Ltac as11 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate11 |( step11 Hyp ; try immediate11)]).

Ltac setParallelogramm11 A B C D := match goal with
	| Hac : A <> C |- _ => match goal with
		|  Hbk : B <> MidPoint A C Hac |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
				fold D in Hyp)
		|  Hbk : B = MidPoint A C Hac -> False |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
				fold D in Hyp)
		|  Hkb : MidPoint A C Hac <> B |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) (sym_not_eq Hkb));
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac (sym_not_eq Hkb))); 
				fold D in Hyp)
		|  Hkb : MidPoint A C Hac= B -> False |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) (sym_not_eq Hkb));
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac (sym_not_eq Hkb))); 
				fold D in Hyp)
		| _ => let K := fresh in (
			pose (K := MidPoint A C Hac);
			let Hbk := fresh in (
				assert (Hbk : B <> MidPoint A C Hac);
				[try immediate11 |
				pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
				let Hyp := fresh in (
					assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
					fold D in Hyp;
					fold K in Hbk, D)]))
		end
	| Hac : A = C -> False |- _ => match goal with
		|  Hbk : B <> MidPoint A C Hac |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
				fold D in Hyp)
		|  Hbk : B = MidPoint A C Hac -> False |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
				fold D in Hyp)
		|  Hkb : MidPoint A C Hac <> B |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) (sym_not_eq Hkb));
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac (sym_not_eq Hkb))); 
				fold D in Hyp)
		|  Hkb : MidPoint A C Hac= B -> False |- _ => pose (D := SymmetricPoint B (MidPoint A C Hac) (sym_not_eq Hkb));
				let Hyp := fresh in (assert (Hyp := (ParallelogrammVertex4 A B C Hac (sym_not_eq Hkb))); 
				fold D in Hyp)
		| _ => let K := fresh in (
			pose (K := MidPoint A C Hac);
			let Hbk := fresh in (
				assert (Hbk : B <> MidPoint A C Hac);
				[try immediate11 |
				pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
				let Hyp := fresh in (
					assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
					fold D in Hyp;
					fold K in Hbk, D)]))
		end

	| Hca : C <> A |- _ => let K := fresh in (
		pose (K := MidPoint A C (sym_not_eq Hca));
		let Hbk := fresh in (
			assert (Hbk : B <> MidPoint A C (sym_not_eq Hca));
			[try immediate11 |
			pose (D := SymmetricPoint B (MidPoint A C (sym_not_eq Hca)) Hbk);
			let Hyp := fresh in (
				assert (Hyp := (ParallelogrammVertex4 A B C (sym_not_eq Hca) Hbk)); 
				fold D in Hyp;
				fold K in Hbk, D)]))
	| Hca : C = A -> False |- _ => let K := fresh in (
		pose (K := MidPoint A C (sym_not_eq Hca));
		let Hbk := fresh in (
			assert (Hbk : B <> MidPoint A C (sym_not_eq Hca));
			[try immediate11 |
			pose (D := SymmetricPoint B (MidPoint A C (sym_not_eq Hca)) Hbk);
			let Hyp := fresh in (
				assert (Hyp := (ParallelogrammVertex4 A B C (sym_not_eq Hca) Hbk)); 
				fold D in Hyp;
				fold K in Hbk, D)]))
	| _ => let Hac := fresh in (
		assert (Hac : A <> C);
		[ try immediate11 |
		 let K := fresh in (
		pose (K := MidPoint A C Hac);
		let Hbk := fresh in (
			assert (Hbk : B <> MidPoint A C Hac);
			[try immediate11 |
			pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
			let Hyp := fresh in (
				assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
				fold D in Hyp;
				fold K in Hbk, D)]))])
end.

Ltac setStrictParallelogramm11 A B C D := match goal with
	| H : Clockwise A B C |- _ => pose (D := StrictPVertex4 A B C H);
		let Hyp := fresh in (
			pose (Hyp := (StrictPVertex4Parallelogramm A B C H)); 
			fold D in Hyp)

	| H : Clockwise B C A |- _ => pose (D := StrictPVertex4 A B C (ClockwiseCAB B C A H));
		let Hyp := fresh in  (
			pose (Hyp := (StrictPVertex4Parallelogramm A B C  (ClockwiseCAB B C A H))); 
			fold D in Hyp)

	| H : Clockwise C A B |- _ => pose (D := StrictPVertex4 A B C  (ClockwiseBCA C A B H));
		let Hyp := fresh in  (
			pose (Hyp := (StrictPVertex4Parallelogramm A B C  (ClockwiseBCA C A B H))); 
			fold D in Hyp)

	| _ => let H := fresh in (
		assert (H :Clockwise A B C);
		[ try immediate11 |
		 pose (D := StrictPVertex4 A B C H);
		let Hyp := fresh in  (
			pose (Hyp := (StrictPVertex4Parallelogramm A B C H)); 
			fold D in Hyp)])
end.

Ltac setParallelogramm11Center11 A B C D K := match goal with
| H : Parallelogramm A B C D |- _ => pose (K := PCenter A B C D H);
	let Hyp1 := fresh in (
		assert (Hyp1 := PCenterBetweenAC A B C D H);
		let Hyp2 := fresh in (
			assert (Hyp2 := PCenterBetweenBD A B C D H);
			let Hyp3 := fresh in (
				assert (Hyp3 := PCenterEqDistanceAC A B C D H);
				let Hyp4 := fresh in (
					assert (Hyp4 := PCenterEqDistanceBD A B C D H);
					fold K in Hyp1, Hyp2, Hyp3, Hyp4))))
| _ => let H := fresh in (
	assert (H : Parallelogramm A B C D);
	[try immediate11 |
		pose (K := PCenter A B C D H);
		let Hyp1 := fresh in (
			assert (Hyp1 := PCenterBetweenAC A B C D H);
			let Hyp2 := fresh in (
				assert (Hyp2 := PCenterBetweenBD A B C D H);
				let Hyp3 := fresh in (
					assert (Hyp3 := PCenterEqDistanceAC A B C D H);
					let Hyp4 := fresh in (
						assert (Hyp4 := PCenterEqDistanceBD A B C D H);
						fold K in Hyp1, Hyp2, Hyp3, Hyp4))))])
end.

Ltac setStrictParallelogramm11Center11 A B C D K := match goal with
| H : StrictParallelogramm A B C D |- _ => DestructSP11 H;
	pose (K := SPCenter A B C D H);
	assert (Between A K C);
	[unfold K; simpl; apply PCenterBetweenAC |
		assert (Between B K D);
		[unfold K; simpl; apply PCenterBetweenBD |
			assert (Distance K A = Distance K C);
			[unfold K; simpl; apply PCenterEqDistanceAC |
				assert (Distance K B = Distance K D);
				[unfold K; simpl; apply PCenterEqDistanceBD |
					let Hyp1 := fresh in (
						assert (Hyp1 := StrictParallelogrammClockwiseABK A B C D H);
						let Hyp2 := fresh in (
							assert (Hyp2 := StrictParallelogrammClockwiseBCK A B C D H);
							let Hyp3 := fresh in (
								assert (Hyp3 := StrictParallelogrammClockwiseCDK A B C D H);
								let Hyp4 := fresh in (
									assert (Hyp4 := StrictParallelogrammClockwiseDAK A B C D H);
									fold K in Hyp1, Hyp2, Hyp3, Hyp4))))]]]]
end.

