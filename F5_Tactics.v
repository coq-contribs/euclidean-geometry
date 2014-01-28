Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A7_Tactics .
Require Import B1_ClockwiseProp B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B6_EquiDirectedProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection E4_Tactics .
Require Import F1_IntersectionDiameterProp F2_MarkSegment F3_Graduation F4_ArchimedianDistance.

Ltac setInterDiameterPoint5 l c M := match goal with
	| H : Diameter l c |- _ => pose (M := InterDiameterPoint l c H);
			let Hyp1 := fresh in (
				assert (Hyp1 := EquiOrientedInterDiameterPoint l c H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircleInterDiameterPoint l c H);
					let Hyp3 := fresh in (
						assert (Hyp3 := OnLineInterDiameterPoint l c H);
						simpl in *; fold M in Hyp1, Hyp2, Hyp3)))
	| _ => let H := fresh in (
			assert (H : Diameter l c);
			[(simplCircle1; simpl in |- *; try immediate4) |
				pose (M := InterDiameterPoint l c H);
				let Hyp1 := fresh in (
					assert (Hyp1 := EquiOrientedInterDiameterPoint l c H);
					let Hyp2 := fresh in (
						assert (Hyp2 := OnCircleInterDiameterPoint l c H);
						let Hyp3 := fresh in (
							assert (Hyp3 := OnLineInterDiameterPoint l c H);
							simpl in *; fold M in Hyp1, Hyp2, Hyp3)))])
end.

Ltac setSecondInterDiameterPoint5 l c M := match goal with
	| H : Diameter l c |- _ => pose (M := SecondInterDiameterPoint l c H);
			let Hyp1 := fresh in (
				assert (Hyp1 := EquiOrientedSecondInterDiameterPoint l c H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircleSecondInterDiameterPoint l c H);
					let Hyp3 := fresh in (
						assert (Hyp3 := OnLineSecondInterDiameterPoint l c H);
						simpl in *; fold M in Hyp1, Hyp2, Hyp3)))
	| _ => let H := fresh in (
			assert (H : Diameter l c);
			[(simplCircle1; simpl in |- *; try immediate4) |
				pose (M := SecondInterDiameterPoint l c H);
				let Hyp1 := fresh in (
					assert (Hyp1 := EquiOrientedSecondInterDiameterPoint l c H);
					let Hyp2 := fresh in (
						assert (Hyp2 := OnCircleSecondInterDiameterPoint l c H);
						let Hyp3 := fresh in (
							assert (Hyp3 := OnLineSecondInterDiameterPoint l c H);
							simpl in *; fold M in Hyp1, Hyp2, Hyp3)))])
end.

Ltac setAddSegmentPoint5 A B C D E M := match goal with
| H : A <> B, H0 : Collinear A B C |- _ => pose (M := AddSegmentPoint A B C D E H H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 
			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))

| H : A = B -> False, H0 : Collinear A B C |- _ => pose (M := AddSegmentPoint A B C D E H H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 
			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))

| H : A <> B |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate4 | pose (M := AddSegmentPoint A B C D E H H0); 
		let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
			let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 				let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
					fold M in Hyp1, Hyp2, Hyp3)))])

| H : A = B -> False |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate4 | pose (M := AddSegmentPoint A B C D E H H0); 
		let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
			let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 				let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
					fold M in Hyp1, Hyp2, Hyp3)))])

| H : B <> A, H0 : Collinear A B C |- _ => pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0); 			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))

| H : B = A -> False, H0 : Collinear A B C |- _ => pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0); 			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))

| H : B <> A |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate4 | pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0);			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))])

| H : B = A -> False |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate4 | pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0);			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))])

| H0 : Collinear A B C |- _ => let H := fresh in (assert (H : A<> B) ; 
	[try immediate4 | pose (M := AddSegmentPoint A B C D E H H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))])

|  _ => let H := fresh in (assert (H : A<> B) ; 
	[try immediate4 | let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate4 | pose (M := AddSegmentPoint A B C D E H H0); 
		let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
			let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 				let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
					fold M in Hyp1, Hyp2, Hyp3)))])])

end.

Ltac setMarkSegmentPoint5 A B C D M := match goal with
| H : A <> B |- _ => pose (M := MarkSegmentPoint A B C D H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := EqDistanceMarkSegmentPoint A B C D H); 
		let Hyp2 := fresh in (
			assert (Hyp2 := ClosedRayMarkSegmentPoint A B C D H); 
			fold M in Hyp1, Hyp2))
| H : A = B -> False |- _ => pose (M := MarkSegmentPoint A B C D H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := EqDistanceMarkSegmentPoint A B C D H); 
		let Hyp2 := fresh in (
			assert (Hyp2 := ClosedRayMarkSegmentPoint A B C D H); 
			fold M in Hyp1, Hyp2))
| H : B <> A |- _ => pose (M := MarkSegmentPoint A B C D (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := EqDistanceMarkSegmentPoint A B C D (sym_not_eq H)); 
		let Hyp2 := fresh in (
			assert (Hyp2 := ClosedRayMarkSegmentPoint A B C D (sym_not_eq H)); 
			fold M in Hyp1, Hyp2))
| H : B = A -> False |- _ => pose (M := MarkSegmentPoint A B C D (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := EqDistanceMarkSegmentPoint A B C D (sym_not_eq H)); 
		let Hyp2 := fresh in (
			assert (Hyp2 := ClosedRayMarkSegmentPoint A B C D (sym_not_eq H)); 
			fold M in Hyp1, Hyp2))
| _ => let Hyp := fresh in (
	assert (Hyp : A<> B) ; 
	[try immediate4 | pose (M := MarkSegmentPoint A B C D Hyp); 
		let Hyp1 := fresh in (
			assert (Hyp1 := EqDistanceMarkSegmentPoint A B C D Hyp); 
			let Hyp2 := fresh in (
				assert (Hyp2 := ClosedRayMarkSegmentPoint A B C D Hyp); 
				fold M in Hyp1, Hyp2))])
end.

Ltac setOppSegmentPoint5 A B C D M := match goal with
	| H : A <> B |- _ => pose (M := OppSegmentPoint A B C D H); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceOppSegmentPoint A B C D H); 
					let Hyp2 := fresh in (
						assert (Hyp2 := SegmentOppSegmentPoint A B C D H); 
						fold M in Hyp1, Hyp2))
	| H : A = B -> False |- _ => pose (M := OppSegmentPoint A B C D H); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceOppSegmentPoint A B C D H); 
					let Hyp2 := fresh in (
						assert (Hyp2 := SegmentOppSegmentPoint A B C D H); 
						fold M in Hyp1, Hyp2))
	| H : B <> A |- _ => pose (M := OppSegmentPoint A B C D (sym_not_eq H)); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceOppSegmentPoint A B C D (sym_not_eq H)); 
					let Hyp2 := fresh in (
						assert (Hyp2 := SegmentOppSegmentPoint A B C D (sym_not_eq H)); 
						fold M in Hyp1, Hyp2))
	| H : B = A -> False |- _ => pose (M := OppSegmentPoint A B C D (sym_not_eq H)); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceOppSegmentPoint A B C D (sym_not_eq H)); 
					let Hyp2 := fresh in (
						assert (Hyp2 := SegmentOppSegmentPoint A B C D (sym_not_eq H)); 
						fold M in Hyp1, Hyp2))
	| _ => let Hyp := fresh in (
				assert (Hyp : A<> B) ; 
				[try immediate4  | pose (M := OppSegmentPoint A B C D Hyp); 
					let Hyp1 := fresh in (
						assert (Hyp1 := EqDistanceOppSegmentPoint A B C D Hyp); 
						let Hyp2 := fresh in (
							assert (Hyp2 := SegmentOppSegmentPoint A B C D Hyp); 
							fold M in Hyp1, Hyp2))])
end.

Ltac setSymmetricPoint5 A B M := match goal with
	| H : A <> B |- _ => pose (M := SymmetricPoint A B H); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceSymmetricPoint A B H); 
					let Hyp2 := fresh in (
						assert (Hyp2 := BetweenSymmetricPoint A B H); 
						fold M in Hyp1, Hyp2))
	| H : A = B -> False |- _ => pose (M := SymmetricPoint A B H); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceSymmetricPoint A B H); 
					let Hyp2 := fresh in (
						assert (Hyp2 := BetweenSymmetricPoint A B H); 
						fold M in Hyp1, Hyp2))
	| H : B <> A |- _ => pose (M := SymmetricPoint A B (sym_not_eq H)); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceSymmetricPoint A B (sym_not_eq H)); 
					let Hyp2 := fresh in (
						assert (Hyp2 := BetweenSymmetricPoint A B (sym_not_eq H)); 
						fold M in Hyp1, Hyp2))
	| H : B = A -> False |- _ => pose (M := SymmetricPoint A B (sym_not_eq H)); 
				let Hyp1 := fresh in (
					assert (Hyp1 := EqDistanceSymmetricPoint A B (sym_not_eq H)); 
					let Hyp2 := fresh in (
						assert (Hyp2 := BetweenSymmetricPoint A B (sym_not_eq H)); 
						fold M in Hyp1, Hyp2))
	| _ => let Hyp := fresh in (
				assert (Hyp : A<> B) ; 
				[try immediate4  | pose (M := SymmetricPoint A B Hyp); 
					let Hyp1 := fresh in (
						assert (Hyp1 := EqDistanceSymmetricPoint A B Hyp); 
						let Hyp2 := fresh in (
							assert (Hyp2 := BetweenSymmetricPoint A B Hyp); 
							fold M in Hyp1, Hyp2))])
end.

Ltac setGraduationPoint5 n A B M := match goal with
	| H : A <> B |- _ => pose (M := Graduation n A B H); 
				let Hyp1 := fresh in (
					assert (Hyp1 := GraduationClosedRay n A B H); 
					let Hyp2 := fresh in (
						assert (Hyp2 := DistanceGraduation n A B H); 
						fold M in Hyp1, Hyp2))
	| H : A = B -> False |- _ => pose (M := Graduation n A B H); 
				let Hyp1 := fresh in (
					assert (Hyp1 := GraduationClosedRay n A B H); 
					let Hyp2 := fresh in (
						assert (Hyp2 := DistanceGraduation n A B H); 
						fold M in Hyp1, Hyp2))
	| H : B <> A |- _ => pose (M := Graduation n A B (sym_not_eq H)); 
				let Hyp1 := fresh in (
					assert (Hyp1 := GraduationClosedRay n  A B (sym_not_eq H)); 
					let Hyp2 := fresh in (
						assert (Hyp2 := DistanceGraduation n A B (sym_not_eq H)); 
						fold M in Hyp1, Hyp2))
	| H : B = A -> False |- _ => pose (M := Graduation n A B (sym_not_eq H)); 
				let Hyp1 := fresh in (
					assert (Hyp1 := GraduationClosedRay n  A B (sym_not_eq H)); 
					let Hyp2 := fresh in (
						assert (Hyp2 := DistanceGraduation n A B (sym_not_eq H)); 
						fold M in Hyp1, Hyp2))
	| _ => let Hyp := fresh in (
				assert (Hyp : A<> B) ; 
				[try immediate4  | pose (M := Graduation n A B Hyp); 
					let Hyp1 := fresh in (
						assert (Hyp1 := GraduationClosedRay n  A B Hyp); 
						let Hyp2 := fresh in (
						assert (Hyp2 := DistanceGraduation n A B Hyp); 
							fold M in Hyp1, Hyp2))])
end.

Ltac immDistinct5 := match goal with
	| H : ?A <> ?B |- ?A <> ?B => exact H
	| H : ?A <> ?B |- ?B <> ?A => auto
	| H : ?A = ?B -> False |- ?A <> ?B => exact H
	| H : ?A = ?B -> False |- ?B <> ?A => auto

	| |- Oo <> Uu => exact DistinctOoUu
	| |- Uu <> Oo => apply sym_not_eq; exact DistinctOoUu

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
end.

Ltac immEquiOriented5 := match goal with
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

	| |- EquiOriented ?A _ _ _ => unfold A; immEquiOriented4
	| |- EquiOriented _ ?A _ _ => unfold A; immEquiOriented4
	| |- EquiOriented _ _ ?A _ => unfold A; immEquiOriented4
	| |- EquiOriented _ _ _ ?A => unfold A; immEquiOriented4
end.

Ltac immCollinear5 := match goal with
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

Ltac immOpenRay5 := match goal with 
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
end.

Ltac immClosedRay5 := apply OpenRayClosedRay; immOpenRay5.

Ltac immBetween5 :=  match goal with
	| H : Between ?A ?B ?C |- Between ?A ?B ?C => exact H
	| H : Between ?C ?B ?A |- Between ?A ?B ?C => apply (BetweenSym _ _ _ H)

	| |- Between ?C (FourPointsInterPoint _ _ ?C ?D _ _) ?D => apply FourPointsInterPointBetweenCD
	| |- Between ?D (FourPointsInterPoint _ _ ?C ?D _ _) ?C => apply BetweenSym; apply FourPointsInterPointBetweenCD

	| |- Between ?A ?B (SymmetricPoint ?A ?B _) => apply BetweenSymmetricPoint
	| |- Between  (SymmetricPoint ?A ?B _) ?B ?A => apply BetweenSym; apply BetweenSymmetricPoint

	| |- Between (Graduation ?n ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab) (Graduation (S (S ?n)) ?A ?B ?Hab) => apply GraduationBetweennSnSSn
	| |- Between (Graduation (S (S ?n)) ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab) (Graduation ?n ?A ?B ?Hab) => apply BetweenSym; apply GraduationBetweennSnSSn

	| |- Between ?B _ _ => unfold B; immBetween5
	| |- Between _ ?B _ => unfold B; immBetween5
	| |- Between _ _ ?B => unfold B; immBetween5
end.

Ltac immSegment5 := match goal with
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

	| |- Segment _ _ _  => apply BetweenSegment; immBetween5
	| |- Segment _ _ _  =>  apply SegmentSym; apply BetweenSegment ; immBetween5

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immOnCircle5 := match goal with 
	| H : OnCircle ?c ?A |- OnCircle ?c ?A => exact H

	| |- OnCircle ?c (IntersectionCirclesPoint ?c _ _) => apply OnCircle1IntersectionCirclesPoint
	| |- OnCircle ?c (IntersectionCirclesPoint _ ?c _) => apply OnCircle2IntersectionCirclesPoint

	| |- OnCircle ?c (InterDiameterPoint _ ?c _) => apply OnCircleInterDiameterPoint

	| |- OnCircle ?c (SecondInterDiameterPoint _ ?c _) => apply OnCircleSecondInterDiameterPoint

	| |- OnCircle (Compass _ _ _) _ => simpl; solveDistance2
	| |- OnCircle ?c _ => unfold c; simpl; solveDistance2
end.

Ltac immOnLine5 := match goal with
	| H : OnLine ?d ?A |- OnLine ?d ?A => exact H
	| |- OnLine ?d (LineA ?d) => destruct d; simpl; immediate4
	| |- OnLine ?d (LineB ?d) => destruct d; simpl; immediate4

	| |- OnLine ?d (InterLinesPoint ?d _ _) => apply OnLine1InterLinesPoint
	| |- OnLine ?d (InterLinesPoint _ ?d _) => apply OnLine2InterLinesPoint
	| |- OnLine ?d (InterDiameterPoint ?d _ _) => apply OnLineInterDiameterPoint
	| |- OnLine ?d (SecondInterDiameterPoint ?d _ _) => apply OnLineSecondInterDiameterPoint

	| |- OnLine (Ruler _ _ _) _ => simpl; immediate4
	| |- OnLine ?d _ => unfold d; simpl; immediate4
end.

Ltac solveEq5 := match goal with
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

	| |- ?A = ?B => match type of A with
			| Point => let H := fresh in (assert (H : Distance A B = Oo); [solveDistance2 | apply (NullDistanceEq A B H)])
			end

	| |- ?X = _ => unfold X; solveEq5
	| |- _ = ?Y => unfold Y; solveEq5
end.

Ltac simplDistance5 := intros; simplCircle2; repeat 
(match goal with 
	| H : context [(Distance ?X ?X)] |- _ => rewrite (NullDistance X) in H
	| |- context [(Distance ?X ?X)] => rewrite (NullDistance X) 

	| H : context [(Distance Oo Uu)] |- _ => rewrite UnitDistance in H
	| |- context [(Distance Oo Uu)] => rewrite UnitDistance 
	| H : context [(Distance Uu Oo)] |- _ => rewrite (DistanceSym Uu Oo) in H; rewrite UnitDistance in H
	| |- context [(Distance Uu Oo)] => rewrite (DistanceSym Uu Oo); rewrite UnitDistance 

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

Ltac solveDistance5 := try simplDistance5; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus2
	| |- _ = DistancePlus _ _ => solveDistPlus2

	| |- DistanceTimes _ _ _ = _ => solveDistTimes2
	| |- _ = DistanceTimes _ _ _ => solveDistTimes2

	| |- Distance _ _ = _ => solveDist2
	| |- _ = Distance _ _ => apply sym_eq; solveDist2

	| |- _ => solveEq5
end.

Ltac immediate5 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate5
	| |- ?A \/ ?B => (left; immediate5)  || (right; immediate5)

	| |- DistancePlus _ _ = _ => solveDistance5
	| |- _ = DistancePlus _ _ => solveDistance5

	| |- DistanceTimes _ _ _ = _ => solveDistance5
	| |- _ = DistanceTimes _ _ _ => solveDistance5

	| |- Distance _ _ = _ => solveDistance5
	| |- _ = Distance _ _ => solveDistance5

	| |- IsDistance ?d => immIsDistance2 d

	| |- _ = _ => solveEq5
	| |- _ <> _ => immDistinct5
	| |- ?A = ?B -> False => fold(A <> B); immDistinct5

	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise3
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise3

	| |- Collinear _ _ _ => immCollinear5
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1

	| |- EquiOriented _ _ _ _ => immEquiOriented5
	| |- OpenRay _ _ _ => immOpenRay5
	| |- ClosedRay _ _ _ => immClosedRay5
	| |- Between _ _ _ => immBetween5
	| |- Segment _ _ _ => immSegment5

	| |- EquiDirected _ _ _ _ => immEquiDirected1
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected4
	| |- EquiDirected ?A ?B ?C ?D  -> False =>fold (~EquiDirected A B C D); immNotEquiDirected4

	| |- DistanceLe _ _ => immDistanceLe2
	| |- DistanceLt _ _ => immDistanceLt3

	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality3
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec3

	| |- Diameter _ _ => immDiameter2
	| |- SecantLines _ _ => immSecantLines4

	| |- OnCircle _ _ => immOnCircle5
	| |- OnLine _ _ => immOnLine5
end.

Ltac byDefEqPoint5 := match goal with
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
end.

Ltac stepEq5 X Y H  := match type of H with
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

	| Distance X Y = _ => apply NullDistanceEq; rewrite H; try immediate5
	| _ = Distance X Y => apply NullDistanceEq; rewrite <- H; try immediate5
	| Distance Y X = _ => apply sym_eq; apply NullDistanceEq; rewrite H; try immediate5
	| _ = Distance Y X => apply sym_eq; apply NullDistanceEq; rewrite <- H; try immediate5

	| DistancePlus (Distance ?A ?B) (Distance X Y) = _ => apply (DistancePlusRightCancell A B X Y); rewrite H; try immediate5
	| DistancePlus (Distance ?A ?B) (Distance Y X) = _ => apply sym_eq; apply (DistancePlusRightCancell A B Y X); rewrite H; try immediate5
	| _ = DistancePlus (Distance ?A ?B) (Distance X Y) => apply (DistancePlusRightCancell A B X Y); rewrite <- H; try immediate5
	| _ = DistancePlus (Distance ?A ?B) (Distance Y X) => apply sym_eq; apply (DistancePlusRightCancell A B Y X); rewrite <- H; try immediate5

	| DistancePlus (Distance X Y) (Distance ?A ?B) = _ => apply (DistancePlusLeftCancell A B X Y); rewrite H; try immediate5
	| DistancePlus (Distance Y X) (Distance ?A ?B) = _ => apply sym_eq; apply (DistancePlusLeftCancell A B Y X); rewrite H; try immediate5
	| _ = DistancePlus  (Distance X Y) (Distance ?A ?B) => apply (DistancePlusLeftCancell A B X Y); rewrite <- H; try immediate5
	| _ = DistancePlus (Distance Y X) (Distance ?A ?B) => apply sym_eq; apply (DistancePlusLeftCancell A B Y X); rewrite <- H; try immediate5

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

Ltac step5 H := match goal with
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

	| |- ?A = ?B => stepEq5 A B H
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

Ltac since5 txt := assert txt; try immediate5.

Ltac from5 H txt := assert txt; [(step5 H ; try immediate5) |  try immediate5].

Ltac as5 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate5 | (step5 Hyp ; try immediate5)]).
