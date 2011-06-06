Require Export geom.

(* Par contraposition avec l'hypothese "H" : *)
Ltac contrapose H := let Hyp := fresh in 
	(intro Hyp; apply H; generalize Hyp; clear Hyp H);
	intro H. 


Ltac visibleConj := match goal with 
	| |- ?A /\ ?B => split 
end.

(*  par simplification du but en utilisant les definitions , il vient : *)
Ltac simplGoal := 
	unfold Segment, Between, Collinear, ClosedRay, OpenRay, EquiDirected, EquiOriented, HalfPlane; intros.

(* par simplification en utilisant les definitions relatives a la droite, il vient *)

Ltac simplLine  :=
	unfold SecantLines, ParallelLines in *; simpl OnLine in *;simpl LineH in *; simpl LineB in *; simpl LineA in *.

(* par simplification en utilisant les definitions relatives au cercle, il vient *)

Ltac simplCircle := unfold uCircle in *; repeat match goal with
	| H: context [(Diameter _ _)] |- _ => unfold Diameter in H; simpl OnLine in H
	| |- context [(Diameter _ _)]  => 	unfold Diameter; simpl OnLine 
	| H: context [(SecantCircles _ _)] |- _ => unfold SecantCircles in H; decompose [and] H; clear H
	| |- context [(SecantCircles _ _)]  => unfold SecantCircles
end;
	simpl OnCircle in *; simpl Radius in *; simpl RadiusB in *; simpl RadiusA in *; simpl Center in *; repeat visibleConj.

Ltac simplCircleHyp H :=
	unfold Diameter, SecantCircles, TriangleSpec in H; simpl RadiusB in H; simpl RadiusA in H; simpl Center in H.

(* par simplification en utilisant les definitions relatives a l'orientation, il vient *)

Ltac canonize := 
	unfold Segment, Between, Collinear, ClosedRay, OpenRay, EquiDirected, EquiOriented, HalfPlane in *; intuition.

Ltac splitIsAngle := repeat (match goal with
	| H : IsAngle _ |- _ => unfold IsAngle in H; decompose [and] H
end); repeat (match goal with
	| H : OnCircle uCircle ?beta /\ ~Clockwise Uu ?beta Oo |- _ => fold (IsAngle beta) in H
end).

Ltac simplDistance := intros; splitIsAngle; simplCircle; repeat 
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

Ltac generalizeMid := repeat match goal with 
	| |- context[MidPoint ?A ?B ?H] => generalize (MidPointEqDistance A B H); let J := fresh in (pose (J := MidPoint A B H); fold J)
end.

(* Un parallelogramme strict est un parallelogramme. *)

Ltac destructSP H := let Hp := fresh in let Hc := fresh in 
	((dependent inversion H as (Hp,Hc) || inversion H as (Hp,Hc)); simpl; clear H; pose (H := SPDef Hp Hc)).

Ltac generalizeDistParallelogramm := repeat match goal with
	| H : Parallelogramm ?A ?B ?C ?D  |- _ => 
		generalize (ParallelogrammABeqCD A B C D H);
		generalize (ParallelogrammBCeqDA A B C D H);
		generalize H; clear H

	| H : StrictParallelogramm ?A ?B ?C ?D  |- _ => destructSP H;
		generalize H; clear H
end.

Ltac generalizeDistTCongruent := repeat match goal with
	| H : TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) |- _ => 
		generalize (TCongruentEqSidesAB A B C D E F H);
		generalize (TCongruentEqSidesBC A B C D E F H);
		generalize (TCongruentEqSidesCA A B C D E F H);
		generalize H; clear H
end.

Ltac generalizeDistIsosceles := repeat match goal with
	| H : Isosceles1 _ |- _ => generalize H; simpl in H; generalize H; clear H
	| H : Isosceles2 _ |- _ => generalize H; simpl in H; generalize H; clear H
	| H : Isosceles3 _ |- _ => generalize H; simpl in H; generalize H; clear H

	| H : Equilateral (Tr ?A ?B ?C) |- _ => 
		generalize (EquilateralEqSides12 A B C H); 
		generalize (EquilateralEqSides23 A B C H); 
		generalize (EquilateralEqSides31 A B C H);
		generalize H; clear H
end.

Ltac generalizeDistance := repeat
match goal with 
	| H : context[(Distance _ _)] |- _ => generalize H; clear H
	| H : context[(DistancePlus _ _)] |- _ => generalize H; clear H
	| H : context[(DistanceTimes _ _ _)] |- _ => generalize H; clear H
end.

Ltac foldDistance := 
repeat (match goal with
| |- context [(Distance ?A ?B)] => try rewrite (DistanceSym B A); 
		let delta := fresh "delta" in (pose (delta := Distance A B); fold delta)
end).

Ltac substDistance :=  repeat 
(let Heq := fresh "Heq" in (
intro Heq;
match type of Heq with 
	| ?X = ?Y  => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| Distance _ _ = _ =>clear H; rewrite Heq
		| _ => fail
		end)
	| ?X = ?Y  => let H := fresh in (assert (H := refl_equal Y); unfold Y in H; match type of H with
		| Distance _ _ = _ =>clear H; rewrite <- Heq
		| _ => fail
		end)
	| _ => fail
end) || intro).

Ltac unfactorizeDistance delta := repeat (match goal with
	| |- context [(DistancePlus ?X delta)] => match X with
		| Distance _ _ => fail
		| DistanceTimes _ _ _ => fail
		| Distance delta delta  => fail
		|  _  => rewrite (DistancePlusCommut X delta)
		end
	| |- context [(DistancePlus?X  (DistancePlus delta ?Y))] => match X with
		|  delta => fail
		| Distance _ _ => fail
		| DistanceTimes _ _ _ => fail
		|  _  => rewrite (DistancePlusAssoc X delta Y); 
			rewrite (DistancePlusCommut X delta);
			rewrite <- DistancePlusAssoc
		end
end).

Ltac unfoldDistance := 
 repeat rewrite <- DistancePlusAssoc;
repeat match goal with 
	| X : Point |- _ => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| Distance _ _ = _ =>clear H; unfactorizeDistance X; subst X
		| _ => fail
		end)
end.

Ltac headDistancePlus B X := match X with
	| (DistancePlus B ?Z) => idtac
	| (DistancePlus ?Z B) => rewrite (DistancePlusCommut Z B)
	| (DistancePlus ?Y ?Z) => headDistancePlus B Z; rewrite (DistancePlusAssoc Y B); rewrite (DistancePlusCommut Y B); rewrite <- (DistancePlusAssoc B Y)
end.

Ltac writeDistancePlus A B sigma := repeat
match goal with
	| |- context [(DistancePlus A B)] => fold sigma
	| |- context [(DistancePlus A (DistancePlus B ?X))] => rewrite (DistancePlusAssoc A B X); fold sigma
	| |- context [(DistancePlus A ?X)] => headDistancePlus B X; rewrite (DistancePlusAssoc A B); fold sigma
end.

Ltac foldDistancePlusRec A B := match B with
	| DistancePlus ?C ?D => foldDistancePlusRec C D
	| _ => let sigma := fresh "sigma" in (pose (sigma := DistancePlus A B); writeDistancePlus A B sigma)
end.

Ltac foldDistancePlus := 
repeat (match goal with
| |- context [(DistancePlus ?A ?B)] => foldDistancePlusRec A B
end).

Ltac unfoldDistancePlus :=  repeat match goal with 
	| X : Point |- _ => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| DistancePlus _ _ = _ =>clear H; subst X
		| DistanceTimes _ _ _ = _ =>clear H; subst X
		| Distance _ _ = _ =>clear H; subst X
		| _ => fail
		end)
end.

Ltac substDistancePlus :=  repeat 
(let Heq := fresh "Heq" in (
intro Heq;
match type of Heq with 
	| DistancePlus _ _ = _ => rewrite Heq
	| _ = DistancePlus _ _ => rewrite <- Heq
	| _ => fail
end) || intro);
 repeat rewrite <- DistancePlusAssoc.

Ltac solveEqBase := match goal with
	| |- ?X = ?X => apply refl_equal
	| H : ?X = ?Y |- ?X = ?Y => exact H
	| H : ?Y = ?X |- ?X = ?Y => rewrite H; apply refl_equal

	| |- ?X = _ => unfold X; solveEqBase
	| |- _ = ?Y => unfold Y; solveEqBase
end.

Ltac solveDistPlus := try generalizeMid;  generalizeDistParallelogramm ; generalizeDistTCongruent; generalizeDistIsosceles; generalizeDistance; foldDistance; substDistance; generalizeDistance;  unfoldDistance; foldDistancePlus; unfoldDistancePlus; substDistancePlus; solveEqBase.

Ltac foldDistanceTimes := 
repeat (match goal with
| |- context [(DistanceTimes ?n ?A ?B)] => try rewrite (DistanceTimesSym B A n); 
		let delta := fresh "delta" in (pose (delta := DistanceTimes n  A B); fold delta)
end).

Ltac unfoldDistanceTimes := 
repeat match goal with 
	| X : Point |- _ => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| DistanceTimes _  _ _ = _ =>clear H; subst X
		| _ => fail
		end)
end.

Ltac substDistanceTimes :=  repeat 
(let Heq := fresh "Heq" in (
intro Heq;
match type of Heq with 
	| DistanceTimes _  _ _ = _ => rewrite Heq
	| _ = DistanceTimes _ _ _ => rewrite <- Heq
	| _ => fail
end) || intro).

Ltac solveDistTimes := try generalizeMid;  generalizeDistParallelogramm ; generalizeDistTCongruent; generalizeDistIsosceles; generalizeDistance; foldDistance; substDistance; generalizeDistance;  unfoldDistance; foldDistanceTimes; unfoldDistanceTimes; substDistanceTimes; solveEqBase.

Ltac solveOnCircleDist := match goal with
	| H : OnCircle (Compass _ _ _) ?A |- Distance ?A _ = _ => unfold OnCircle in H
	| H : OnCircle (Compass _ _ _) ?A |- Distance _ ?A = _ => unfold OnCircle in H
	| H : OnCircle (Compass _ _ _) ?A |- _ = Distance ?A _ => unfold OnCircle in H
	| H : OnCircle (Compass _ _ _) ?A |- _ = Distance _ ?A => unfold OnCircle in H
	| H : OnCircle ?c ?A |- Distance ?A _ = _ => unfold c, OnCircle in H
	| H : OnCircle ?c ?A |- Distance _ ?A = _ => unfold c, OnCircle in H
	| H : OnCircle ?c ?A |- _ = Distance ?A _ => unfold c, OnCircle in H
	| H : OnCircle ?c ?A |- _ = Distance _ ?A => unfold c, OnCircle in H
end.

Ltac solveDist :=try solveOnCircleDist; try generalizeMid; generalizeDistParallelogramm ; generalizeDistTCongruent; generalizeDistIsosceles; generalizeDistance; foldDistance; substDistance;  unfoldDistance; solveEqBase.

(* Par calcul sur les distances *)

Ltac solveDistance := simplDistance; match goal with
	| |- ?X = ?X => apply refl_equal
	| H : ?X = ?Y |- ?X = ?Y => exact H
	| H : ?Y = ?X |- ?X = ?Y => rewrite H; apply refl_equal

	| |- DistancePlus _ _ = _ => solveDistPlus
	| |- _ = DistancePlus _ _ => solveDistPlus

	| |- DistanceTimes _ _ _ = _ => solveDistTimes
	| |- _ = DistanceTimes _ _ _ => solveDistTimes

	| |- Distance _ _ = _ => solveDist
	| |- _ = Distance _ _ => apply sym_eq; solveDist
end.

Ltac immOnCircle := match goal with 
	| H : OnCircle ?c ?A |- OnCircle ?c ?A => exact H

	| H : IsAngle ?A |- OnCircle uCircle ?A => unfold IsAngle in H; intuition

	| |- OnCircle ?c (IntersectionCirclesPoint ?c _ _) => apply OnCircle1IntersectionCirclesPoint
	| |- OnCircle ?c (IntersectionCirclesPoint _ ?c _) => apply OnCircle2IntersectionCirclesPoint

	| |- OnCircle ?c (InterDiameterPoint _ ?c _) => apply OnCircleInterDiameterPoint
	| |- OnCircle ?c (SecondInterDiameterPoint _ ?c _) => apply OnCircleSecondInterDiameterPoint

	| |- OnCircle (Compass _ _ _) _ => simpl; solveDist
	| |- OnCircle ?c _ => unfold c; simpl; solveDist
end.

Ltac immClockwise := match goal with
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

Ltac immCollinearBase := match goal with
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

	| |- Collinear ?A _ _ => unfold A; immCollinearBase
	| |- Collinear _ ?B _ => unfold B; immCollinearBase
	| |- Collinear _ _ ?C => unfold C; immCollinearBase
end.

Ltac immCollinear := immCollinearBase ||  match goal with
	| H : NullAngle ?B ?A ?C |- Collinear ?A ?B ?C => apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?B ?A ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply OpenRayCollinear; apply (NullAngleOpenRay A B C H)

	| H : ElongatedAngle ?A ?B ?C |- Collinear ?A ?B ?C => apply BetweenCollinear; apply (ElongatedAngleBetween B A C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?A ?C ?B => apply CollinearACB; apply BetweenCollinear; apply (ElongatedAngleBetween B A C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?B ?A ?C => apply CollinearBAC; apply BetweenCollinear; apply (ElongatedAngleBetween B A C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?B ?C ?A => apply CollinearBCA; apply BetweenCollinear; apply (ElongatedAngleBetween B A C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?C ?A ?B => apply CollinearCAB; apply BetweenCollinear; apply (ElongatedAngleBetween B A C H)
	| H : ElongatedAngle ?A ?B ?C |- Collinear ?C ?B ?A => apply CollinearCBA; apply BetweenCollinear; apply (ElongatedAngleBetween B A C H)

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

	| |- Collinear (InterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immCollinearBase
	| |- Collinear _ (InterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immCollinearBase
	| |- Collinear _ _ (InterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immCollinearBase

	| |- Collinear (SecondInterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immCollinearBase
	| |- Collinear _ (SecondInterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immCollinearBase
	| |- Collinear _ _ (SecondInterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immCollinearBase

	| |- Collinear (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := CollinearAddSegmentPoint A B C D E H H0); immCollinearBase
	| |- Collinear _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ => let Hyp := fresh in assert (Hyp := CollinearAddSegmentPoint A B C D E H H0); immCollinearBase
	| |- Collinear _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) => let Hyp := fresh in assert (Hyp := CollinearAddSegmentPoint A B C D E H H0); immCollinearBase

	| |- Collinear (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immCollinearBase
	| |- Collinear _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immCollinearBase
	| |- Collinear _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immCollinearBase

	| |- Collinear (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immCollinearBase
	| |- Collinear _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immCollinearBase
	| |- Collinear _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immCollinearBase

	| |- Collinear (SymmetricPoint ?A ?B ?H) _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immCollinearBase
	| |- Collinear _ (SymmetricPoint ?A ?B ?H) _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immCollinearBase
	| |- Collinear _ _ (SymmetricPoint ?A ?B ?H) => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immCollinearBase

	| |- Collinear (MidPoint ?A ?B ?H) _ _ => apply CollinearCAB; apply (MidPointCollinearAB A B H)
	| |- Collinear _ (MidPoint ?A ?B ?H) _ => apply CollinearACB; apply (MidPointCollinearAB A B H)
	| |- Collinear _ _ (MidPoint ?A ?B ?H) =>  apply (MidPointCollinearAB A B H)

	| |- Collinear ?A ?B (Graduation _ ?A ?B _ ) => apply CollinearGraduation
	| |- Collinear ?B ?A (Graduation _ ?A ?B _ ) => apply CollinearBAC; apply CollinearGraduation
	| |- Collinear ?A (Graduation _ ?A ?B _ ) ?B => apply CollinearACB; apply CollinearGraduation
	| |- Collinear ?B (Graduation _ ?A ?B _ ) ?A => apply CollinearBCA; apply CollinearGraduation
	| |- Collinear (Graduation _ ?A ?B _ ) ?A ?B => apply CollinearCAB; apply CollinearGraduation
	| |- Collinear (Graduation _ ?A ?B _ ) ?B  ?A => apply CollinearCBA; apply CollinearGraduation

	| |- Collinear ?A _ _ => unfold A; immCollinear
	| |- Collinear _ ?B _ => unfold B; immCollinear
	| |- Collinear _ _ ?C => unfold C; immCollinear
end.

Ltac immNotClockwise := match goal with
	|  |- ~Clockwise ?A ?A _ => apply NotClockwiseAAB	
	|  |- ~Clockwise ?A _ ?A => apply NotClockwiseABA
	|  |- ~Clockwise _ ?A ?A => apply NotClockwiseABB

	| |- ~Clockwise _ (IntersectionCirclesPoint ?c1 ?c2 ?H) _ => let Hyp := fresh in (
					assert (Hyp := NotClockwiseIntersectionCirclesPoint c1 c2 H);
					simplCircle; exact Hyp)

	|   |- ~Clockwise (Angle ?A ?B ?C ?H1 ?H2) Oo Uu => let Hyp := fresh in assert (Hyp := NotClockwiseAngle A B C H1 H2); immNotClockwise
	|   |- ~Clockwise Oo Uu (Angle ?A ?B ?C ?H1 ?H2) => let Hyp := fresh in assert (Hyp := NotClockwiseAngle A B C H1 H2); immNotClockwise
	|   |- ~Clockwise Uu (Angle ?A ?B ?C ?H1 ?H2) Oo => let Hyp := fresh in assert (Hyp := NotClockwiseAngle A B C H1 H2); immNotClockwise

	| H : IsAngle ?A  |- ~Clockwise ?A Oo Uu => destruct H; immNotClockwise
	| H : IsAngle ?A  |- ~Clockwise Oo Uu ?A => destruct H; immNotClockwise
	| H : IsAngle ?A  |- ~Clockwise Uu ?A Oo => destruct H; immNotClockwise

	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?A ?B ?C => exact H	
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?B ?C ?A => intro; elim H; immClockwise
	| H : ~Clockwise ?A ?B ?C |- ~Clockwise ?C ?A ?B => intro; elim H; immClockwise

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?D => apply (EquiOrientedNotClockwiseABD _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?D ?A => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?D ?A ?B => intro; elim (EquiOrientedNotClockwiseABD _ _ _ _ H); immClockwise

	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?A ?B ?C => apply (EquiOrientedNotClockwiseABC _ _ _ _ H)	
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?B ?C ?A => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise
	| H : EquiOriented ?A ?B ?C ?D |- ~Clockwise ?C ?A ?B => intro; elim (EquiOrientedNotClockwiseABC _ _ _ _ H); immClockwise

	|  |- ~Clockwise ?A ?B ?C => apply ClockwiseNotClockwise; immClockwise
	|  |- ~Clockwise ?A ?B ?C => apply CollinearNotClockwise; immCollinear 
end.

Ltac immOnLine := match goal with
	| H : OnLine ?d ?A |- OnLine ?d ?A => exact H
	| |- OnLine ?d (LineA ?d) => destruct d; simpl; immCollinear
	| |- OnLine ?d (LineB ?d) => destruct d; simpl; immCollinear

	| |- OnLine ?d (InterLinesPoint ?d _ _) => apply OnLine1InterLinesPoint
	| |- OnLine ?d (InterLinesPoint _ ?d _) => apply OnLine2InterLinesPoint
	| |- OnLine ?d (InterDiameterPoint ?d _ _) => apply OnLineInterDiameterPoint
	| |- OnLine ?d (SecondInterDiameterPoint ?d _ _) => apply OnLineSecondInterDiameterPoint

	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?A ?B ?H) => apply MidPointOnMidLine
	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?A ?B ?H') => rewrite (MidPointRefl A B H' H); apply MidPointOnMidLine
	| |- OnLine (MidLine ?A ?B ?H) (MidPoint ?B ?A ?H') =>  rewrite (MidPointSym B A H' H); apply MidPointOnMidLine

	| |- OnLine (MidLine Uu uU DistinctUuuU) Vv => apply OnMidLineVv
	| |- OnLine (MidLine Uu uU DistinctUuuU) RightAngle => unfold RightAngle; apply OnMidLineVv

	| |- OnLine (MidLine ?A ?B ?H) ?M => apply EqDistanceOnMidLine; solveDist

	| |- OnLine ?d (PerpendicularPoint ?d _ _) => apply PerpendicularPointOnLine1
	| |- OnLine ?d (PerpendicularPoint _ ?d _) => apply PerpendicularPointOnLine2

	| |- OnLine  (PerpendicularDown ?d ?A ?H) ?A => apply (PerpendicularDownOnLine d A H)
	| |- OnLine  (PerpendicularUp ?d ?A ?H) ?A => apply (PerpendicularUpOnLine d A H)

	| |- OnLine  (Parallel ?d ?A ?H) ?A => apply (OnLineAParallel d A H)

	| |- OnLine (Ruler _ _ _) _ => simpl; immCollinear
	| |- OnLine ?d _ => unfold d; simpl; immCollinear
end.

Ltac immDistinct := match goal with
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

	| H : DistanceLt ?A ?B |- ?A <> ?B  => let Hyp := fresh in (destruct H  as ((_, _), Hyp); apply Hyp)
	| H : DistanceLt ?A ?B |- ?B <> ?A  => apply sym_not_eq; let Hyp := fresh in (destruct H  as ((_, _), Hyp); apply Hyp)

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

	| H : Supplement ?A ?B _ _ _ _ |- ?B <> ?A => let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp0)
	| H : Supplement ?A ?B _ _ _ _ |- ?A <> ?B => apply sym_not_eq; let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp0)
	| H : Supplement _ ?B ?C _ _ _ |- ?B <> ?C => let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp1)
	| H : Supplement _ ?B ?C _ _ _ |- ?C <> ?B => apply sym_not_eq; let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp1)
	| H : Supplement _ _ _ ?D ?E _ |- ?E <> ?D => let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp2)
	| H : Supplement _ _ _ ?D ?E _ |- ?D <> ?E => apply sym_not_eq; let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp2)
	| H : Supplement _ _ _ _  ?E ?F |- ?E <> ?F => let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp3)
	| H : Supplement _ _ _ _  ?E ?F |- ?F <> ?E => apply sym_not_eq; let Hyp0 := fresh in let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in (inversion H as [Hyp0 Hyp1 Hyp2 Hyp3 _]; exact Hyp3)

	| H : OpposedAngles ?A ?B _ _ _ |- ?B <> ?A => let Hyp := fresh in (inversion H as [Hyp _]; apply (BetweenDistinctAB _ _ _ Hyp))
	| H : OpposedAngles ?A ?B _ _ _ |- ?A <> ?B => apply sym_not_eq; let Hyp := fresh in (inversion H as [Hyp _]; apply (BetweenDistinctAB _ _ _ Hyp))
	| H : OpposedAngles ?B _ ?C _ _ |- ?B <> ?C => apply sym_not_eq; let Hyp := fresh in (inversion H as [_ Hyp]; apply (BetweenDistinctAB _ _ _ Hyp))
	| H : OpposedAngles ?B _ ?C _ _ |- ?C <> ?B => let Hyp := fresh in (inversion H as [_ Hyp]; apply (BetweenDistinctAB _ _ _ Hyp))
	| H : OpposedAngles ?D _ _ ?E _ |- ?E <> ?D => apply sym_not_eq; let Hyp := fresh in (inversion H as [Hyp _]; apply (BetweenDistinctBC _ _ _ Hyp))
	| H : OpposedAngles ?D _ _ ?E _ |- ?D <> ?E => let Hyp := fresh in (inversion H as [Hyp _]; apply (BetweenDistinctBC _ _ _ Hyp))
	| H : OpposedAngles ?E _ _ _ ?F |- ?E <> ?F => let Hyp := fresh in (inversion H as [_ Hyp]; apply (BetweenDistinctBC _ _ _ Hyp))
	| H : OpposedAngles ?E _ _ _ ?F |- ?F <> ?E => apply sym_not_eq; let Hyp := fresh in (inversion H as [_ Hyp]; apply (BetweenDistinctBC _ _ _ Hyp))

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

	| H : Parallelogramm ?A ?B ?C ?D |- ?A <> ?C =>  let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp0 Hyp1 _]; exact Hyp0)
	| H : Parallelogramm ?A ?B ?C ?D |- ?C <> ?A => apply sym_not_eq; let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp0 Hyp1 _]; exact Hyp0)
	| H : Parallelogramm ?A ?B ?C ?D |- ?B <> ?D => let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp0 Hyp1 _]; exact Hyp1)
	| H : Parallelogramm ?A ?B ?C ?D |- ?D <> ?B => apply sym_not_eq; let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp0 Hyp1 _]; exact Hyp1)

	| H : StrictParallelogramm ?A ?B ?C ?D |- ?A <> ?C => let Hyp := fresh in let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp _]; inversion Hyp as [Hyp0 Hyp1 _]; exact Hyp0)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?C <> ?A => apply sym_not_eq; let Hyp := fresh in let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp _]; inversion Hyp as [Hyp0 Hyp1 _]; exact Hyp0)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?B <> ?D => let Hyp := fresh in let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp _]; inversion Hyp as [Hyp0 Hyp1 _]; exact Hyp1)
	| H : StrictParallelogramm ?A ?B ?C ?D |- ?D <> ?B => apply sym_not_eq; let Hyp := fresh in let Hyp0 := fresh in let Hyp1 := fresh in (inversion H as [Hyp _]; inversion Hyp as [Hyp0 Hyp1 _]; exact Hyp1)
end.

Ltac immEquiOrientedBase := match goal with
	| |- EquiOriented ?A ?A ?B ?C => apply EquiOrientedAABC
	| |- EquiOriented ?A ?B ?A ?B => canonize
	| H : EquiOriented ?A ?B ?C ?D |- EquiOriented ?A ?B ?C ?D => trivial
	| H : forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D M |- EquiOriented ?A ?B ?C ?D => trivial

	|  |- EquiOriented Oo (Distance _ _) Oo Uu => apply IsDistanceDistance
	|  |- EquiOriented  Oo Uu Oo (Distance _ _) => apply (ChangeAllABAC _ _ _); [apply IsDistanceDistance | try immDistinct]
	|  |- EquiOriented  Uu Oo (Distance _ _) Oo => apply (ChangeSide _ _ _ _); [apply IsDistanceDistance | try immDistinct]
	|  |- EquiOriented (Distance _ _) Oo Uu Oo => apply (ChangeSenseABAC _ _ _); apply IsDistanceDistance

	|  |- EquiOriented Oo (DistancePlus _ _) Oo Uu => apply IsDistanceDistancePlus
	|  |- EquiOriented  Oo Uu Oo (DistancePlus _ _) => apply (ChangeAllABAC _ _ _); [apply IsDistanceDistancePlus | try immDistinct]
	|  |- EquiOriented  Uu Oo (DistancePlus _ _) Oo => apply (ChangeSide _ _ _ _); [apply IsDistanceDistancePlus | try immDistinct]
	|  |- EquiOriented (DistancePlus _ _) Oo Uu Oo => apply (ChangeSenseABAC _ _ _); apply IsDistanceDistancePlus

	|  |- EquiOriented Oo (DistanceTimes _ _ _) Oo Uu => apply IsDistanceDistanceTimes
	|  |- EquiOriented  Oo Uu Oo (DistanceTimes _ _ _) => apply (ChangeAllABAC _ _ _); [apply IsDistanceDistanceTimes | try immDistinct]
	|  |- EquiOriented  Uu Oo (DistanceTimes _ _ _) Oo => apply (ChangeSide _ _ _ _); [apply IsDistanceDistanceTimes | try immDistinct]
	|  |- EquiOriented (DistanceTimes _ _ _) Oo Uu Oo => apply (ChangeSenseABAC _ _ _); apply IsDistanceDistanceTimes

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?C ?B ?A ?B => apply (ChangeAllABCB _ _ _ H); try immDistinct
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?B ?C ?A ?B => apply (ChangeAllABBC _ _ _ H); try immDistinct
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?C ?A ?A ?B => apply (ChangeAllABCA _ _ _ H); try immDistinct
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented  ?A ?C ?A ?B => apply (ChangeAllABAC _ _ _ H); try immDistinct

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?B ?C ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?C ?B ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?A ?C ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented  ?C ?A ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?B ?A ?B ?C => apply (ChangeSenseABCB _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?B ?A ?C ?B => apply (ChangeSenseABBC _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?B ?A ?A ?C => apply (ChangeSenseABCA _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented ?B ?A ?C ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : OpenRay ?A ?B ?C |- EquiOriented ?A ?B ?A ?C => exact H
	| H : OpenRay ?A ?B ?C |- EquiOriented  ?A ?C ?A ?B => apply (ChangeAllABAC _ _ _ H); try immDistinct
	| H : OpenRay ?A ?B ?C |- EquiOriented  ?C ?A ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct
	| H : OpenRay ?A ?B ?C |- EquiOriented ?B ?A ?C ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : ClosedRay ?A ?B ?C |- EquiOriented ?A ?C ?A ?B => exact H
	| H : ClosedRay ?A ?B ?C |- EquiOriented  ?A ?B ?A ?C => apply (ChangeAllABAC _ _ _ H); try immDistinct
	| H : ClosedRay ?A ?B ?C |- EquiOriented  ?B ?A ?C ?A => apply (ChangeSide _ _ _ _ H); try immDistinct
	| H : ClosedRay ?A ?B ?C |- EquiOriented ?C ?A ?B ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : Between ?A ?B ?C |- EquiOriented ?A ?B ?B ?C => destruct H; trivial
	| H : Between ?A ?B ?C |- EquiOriented ?B ?C ?A ?B => let Hyp1 := fresh in (let Hyp2 := fresh in (destruct H as (Hyp1,Hyp2); apply (ChangeAllABBC _ _ _ Hyp2 Hyp1)))
	| H : Between ?A ?B ?C |- EquiOriented ?C ?B ?B ?A => let Hyp1 := fresh in (let Hyp2 := fresh in (destruct H as (Hyp1,Hyp2); apply (ChangeSide _ _ _ _ Hyp2 Hyp1)))
	| H : Between ?A ?B ?C |- EquiOriented  ?B ?A ?C ?B => let Hyp := fresh in (destruct H as (_,Hyp); apply (ChangeSenseABBC _ _ _ Hyp))

	| H : Archimed ?A ?B ?C |- EquiOriented ?A ?C ?A ?B => apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- EquiOriented  ?A ?B ?A ?C => apply ChangeAllABAC; [apply (ArchimedianClosedRay _ _ _ H) |  try immDistinct]
	| H : Archimed ?A ?B ?C |- EquiOriented  ?B ?A ?C ?A => apply ChangeSide; [apply (ArchimedianClosedRay _ _ _ H) |  try immDistinct]
	| H : Archimed ?A ?B ?C |- EquiOriented ?C ?A ?B ?A => apply ChangeSenseABAC; apply (ArchimedianClosedRay _ _ _ H)
end.

Ltac immEquiOriented := immEquiOrientedBase || match goal with
	| |- EquiOriented (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ _ _ => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOrientedBase
	| |- EquiOriented _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOrientedBase
	| |- EquiOriented _ _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOrientedBase
	| |- EquiOriented _ _ _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) => let Hyp := fresh in assert (Hyp := FourPointsInterPointBetweenCD A B C D H H0); immEquiOrientedBase

	| |- EquiOriented (InterDiameterPoint ?l ?c ?H) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase
	| |- EquiOriented _ (InterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase
	| |- EquiOriented _ _ (InterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase
	| |- EquiOriented _ _ _ (InterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase

	| |- EquiOriented (SecondInterDiameterPoint ?l ?c ?H) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase
	| |- EquiOriented _ (SecondInterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase
	| |- EquiOriented _ _ (SecondInterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase
	| |- EquiOriented _ _ _ (SecondInterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immEquiOrientedBase

	| |- EquiOriented (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOrientedBase
	| |- EquiOriented _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOrientedBase
	| |- EquiOriented _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOrientedBase
	| |- EquiOriented _ _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immEquiOrientedBase

	| |- EquiOriented (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOrientedBase
	| |- EquiOriented _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOrientedBase
	| |- EquiOriented _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOrientedBase
	| |- EquiOriented _ _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immEquiOrientedBase

	| |- EquiOriented (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOrientedBase
	| |- EquiOriented _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOrientedBase
	| |- EquiOriented _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOrientedBase
	| |- EquiOriented _ _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immEquiOrientedBase

	| |- EquiOriented (SymmetricPoint ?A ?B ?H) _ _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOrientedBase
	| |- EquiOriented _ (SymmetricPoint ?A ?B ?H) _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOrientedBase
	| |- EquiOriented _ _ (SymmetricPoint ?A ?B ?H) _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOrientedBase
	| |- EquiOriented _ _ _ (SymmetricPoint ?A ?B ?H) => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immEquiOrientedBase

	| |- EquiOriented (Graduation ?n ?A ?B ?Hab) _ _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOrientedBase
	| |- EquiOriented _ (Graduation ?n ?A ?B ?Hab) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOrientedBase
	| |- EquiOriented _ _ (Graduation ?n ?A ?B ?Hab) _ => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOrientedBase
	| |- EquiOriented _ _ _ (Graduation ?n ?A ?B ?Hab) => let Hyp := fresh in assert (Hyp := EquiOrientedGraduation n A B Hab); immEquiOrientedBase

	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?B ?A ?C ?D => apply (StrictParallelogrammEquiOriented A B C D H)
	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?D ?C ?A ?B => apply (ChangeSide B A C D); [apply (StrictParallelogrammEquiOriented A B C D H) | apply (sym_not_eq (StrictParallelogrammDistinctAB A B C D H))]

	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?C ?B ?D ?A => apply (StrictParallelogrammEquiOriented B C D A (StrictParallelogrammPerm A B C D H))
	| H : StrictParallelogramm ?A ?B ?C ?D |- EquiOriented ?A ?D ?B ?C => apply (ChangeSide C B D A); [apply (StrictParallelogrammEquiOriented B C D A  (StrictParallelogrammPerm A B C D H)) | apply (sym_not_eq (StrictParallelogrammDistinctBC A B C D H))]

	| Hc : Collinear _  _ (PCenter ?A ?B ?C ?D ?H)  |- EquiOriented ?A ?B ?D ?C => apply (FlatParallelogramm A B C D H); immCollinear
	| Hc : Collinear _  (PCenter ?A ?B ?C ?D ?H) _  |- EquiOriented ?A ?B ?D ?C => apply (FlatParallelogramm A B C D H); immCollinear
	| Hc : Collinear  (PCenter ?A ?B ?C ?D ?H) _ _  |- EquiOriented ?A ?B ?D ?C => apply (FlatParallelogramm A B C D H); immCollinear

	| |- EquiOriented ?A _ _ _ => unfold A; immEquiOriented
	| |- EquiOriented _ ?A _ _ => unfold A; immEquiOriented
	| |- EquiOriented _ _ ?A _ => unfold A; immEquiOriented
	| |- EquiOriented _ _ _ ?A => unfold A; immEquiOriented
end.

Ltac immOpenRayBase := match goal with 
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
	| H : Segment ?A ?B ?C |- OpenRay ?A ?B ?C => apply SegmentOpenRayAB; [exact H | immDistinct]
	| H : Segment ?A ?B ?C |- OpenRay ?B ?A ?C => apply SegmentOpenRayAB; [apply (SegmentSym _ _ _ H) | immDistinct]

	| H : DistanceLe ?A ?B |- OpenRay Oo ?A ?B  => let Hyp := fresh in (destruct H  as (Hyp, _); apply Hyp)
	| H : DistanceLe ?A ?B |- OpenRay ?B ?A Oo  => let Hyp := fresh in (destruct H  as (_, Hyp); apply Hyp)

	| H : DistanceLt ?A ?B |- OpenRay Oo ?A ?B  => let Hyp := fresh in (destruct H  as ((Hyp, _), _); apply Hyp)
	| H : DistanceLt ?A ?B |- OpenRay ?B ?A Oo  => let Hyp := fresh in (destruct H  as ((_, Hyp), _); apply Hyp)

	| H : OpenRay ?A ?B ?C |- OpenRay ?A ?C ?B => apply OpenRaySym; [immDistinct | exact H]
	| H : ClosedRay ?A ?B ?C |- OpenRay ?A ?B ?C =>  apply OpenRaySym; [immDistinct | apply ClosedRayOpenRay; exact H]

	| H : Archimed ?A ?B ?C |- OpenRay ?A ?C ?B => apply ClosedRayOpenRay; apply (ArchimedianClosedRay A B C H)
end.

Ltac immOpenRay := immOpenRayBase || match goal with 
	| |- OpenRay (InterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immOpenRayBase
	| |- OpenRay _ (InterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immOpenRayBase
	| |- OpenRay _ _ (InterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedInterDiameterPoint l c H); simplCircle; simplLine; immOpenRayBase

	| |- OpenRay (SecondInterDiameterPoint ?l ?c ?H) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immOpenRayBase
	| |- OpenRay _ (SecondInterDiameterPoint ?l ?c ?H) _ => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immOpenRayBase
	| |- OpenRay _ _ (SecondInterDiameterPoint ?l ?c ?H) => let Hyp := fresh in assert (Hyp := EquiOrientedSecondInterDiameterPoint l c H); simplCircle; simplLine; immOpenRayBase

	| |- OpenRay (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immOpenRayBase
	| |- OpenRay _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) _ => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immOpenRayBase
	| |- OpenRay _ _ (AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0) => let Hyp := fresh in assert (Hyp := EquiOrientedAddSegmentPoint A B C D E H H0); immOpenRayBase

	| |- OpenRay (MarkSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immOpenRayBase
	| |- OpenRay _ (MarkSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immOpenRayBase
	| |- OpenRay _ _ (MarkSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := ClosedRayMarkSegmentPoint A B C D H); immOpenRayBase

	| |- OpenRay (OppSegmentPoint ?A ?B ?C ?D ?H) _ _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immOpenRayBase
	| |- OpenRay _ (OppSegmentPoint ?A ?B ?C ?D ?H) _ => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immOpenRayBase
	| |- OpenRay _ _ (OppSegmentPoint ?A ?B ?C ?D ?H) => let Hyp := fresh in assert (Hyp := SegmentOppSegmentPoint A B C D H); immOpenRayBase

	| |- OpenRay (SymmetricPoint ?A ?B ?H) _ _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immOpenRayBase
	| |- OpenRay _ (SymmetricPoint ?A ?B ?H) _ => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immOpenRayBase
	| |- OpenRay _ _ (SymmetricPoint ?A ?B ?H) => let Hyp := fresh in assert (Hyp := BetweenSymmetricPoint A B H); immOpenRayBase

	| |- OpenRay ?A (Graduation _ ?A ?B _) ?B => apply ClosedRayOpenRay; apply GraduationClosedRay

	| H : NullAngle ?B ?A ?C |- OpenRay ?A ?B ?C => apply (NullAngleOpenRay A B C H)
	| H : NullAngle ?C ?A ?B |- OpenRay ?A ?B ?C => apply (NullAngleOpenRay A B C (NullAngleSym B A C H))
end.

Ltac immClosedRay := apply OpenRayClosedRay; immOpenRay.

Ltac immIsDistance d  := match d with
	| Distance _ _ => apply IsDistanceDistance
	| DistancePlus _ _ => apply IsDistanceDistancePlus
	| DistanceTimes _ _ _ => apply IsDistanceDistanceTimes
	| _ => assumption || (unfold IsDistance; immClosedRay)
end.

Ltac immBetween :=  match goal with
	| |- Between Uu Oo uU => exact BetweenUuOouU
	| |- Between uU Oo Uu => apply BetweenSym; exact BetweenUuOouU

	| H : Between ?A ?B ?C |- Between ?A ?B ?C => exact H
	| H : Between ?C ?B ?A |- Between ?A ?B ?C => apply (BetweenSym _ _ _ H)

	| |- Between ?C (FourPointsInterPoint _ _ ?C ?D _ _) ?D => apply FourPointsInterPointBetweenCD
	| |- Between ?D (FourPointsInterPoint _ _ ?C ?D _ _) ?C => apply BetweenSym; apply FourPointsInterPointBetweenCD

	| |- Between ?A ?B (SymmetricPoint ?A ?B _) => apply BetweenSymmetricPoint
	| |- Between  (SymmetricPoint ?A ?B _) ?B ?A => apply BetweenSym; apply BetweenSymmetricPoint

	| |- Between ?A (Graduation ?n ?A ?B ?Hab) (Graduation (S ?n) ?A ?B ?Hab) => apply GraduationBetweenAnSn; omega
	| |- Between (Graduation (S ?n) ?A ?B ?Hab) (Graduation ?n ?A ?B ?Hab) ?A => apply BetweenSym; apply GraduationBetweenAnSn; omega

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

	| |- Between ?A (SPCenter ?A _ ?C _  ?H) ?C => destructSP H; apply PCenterBetweenAC
	| |- Between ?C (SPCenter ?A _ ?C _  ?H) ?A => destructSP H; apply BetweenSym; apply PCenterBetweenAC
	| |- Between ?B (SPCenter _ ?B _ ?D ?H) ?D => destructSP H; apply PCenterBetweenBD
	| |- Between ?D (SPCenter _ ?B _ ?D ?H) ?B => destructSP H; apply BetweenSym; apply PCenterBetweenBD

	| |- Between ?B _ _ => unfold B; immBetween
	| |- Between _ ?B _ => unfold B; immBetween
	| |- Between _ _ ?B => unfold B; immBetween
end.

Ltac immSegment := match goal with
	| |- Segment ?A ?B ?A => apply SegmentABA
	| |- Segment ?A ?B ?B => apply SegmentABB
	| |- Segment Oo (DistancePlus?A ?B) ?A => apply IsDistanceSegmentDistancePlus; immIsDistance A

	| |- Segment (OppSegmentPoint ?A ?B _ _ _) ?B ?A => apply SegmentOppSegmentPoint
	| |- Segment ?B (OppSegmentPoint ?A ?B _ _ _) ?A => apply SegmentSym; apply SegmentOppSegmentPoint

	| |- Segment ?A (Graduation (S ?n) ?A _ _ ) (Graduation ?n ?A _ _) => apply GraduationSegment
	| |- Segment ?A (Graduation (S ?n) ?A ?B _ ) ?B => apply GraduationSegmentSn
	| |- Segment ?B (Graduation (S (S ?n)) ?A ?B _ ) (Graduation (S ?n) ?A ?B _) => apply GraduationSegmentB

	| H : Segment ?A ?B ?C |- Segment ?A ?B ?C => exact H
	| H : Segment ?A ?B ?C |- Segment ?B ?A ?C => apply (SegmentSym _ _ _ H)

	| H : EquiOriented ?A ?B ?B ?C |- Segment ?A ?C ?B => apply (EquiOrientedSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (EquiOrientedSegment A B C H)

	| |- Segment _ _ _  => apply BetweenSegment; immBetween

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac solveEq := match goal with
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

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle | immOnCircle | immNotClockwise]
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle | immOnCircle | immNotClockwise]

	| |- ?M = InterLinesPoint ?l1 ?l2 ?H => apply (UniqueInterLinesPoint l1 l2 H M); immOnLine
	| |- InterLinesPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueInterLinesPoint l1 l2 H M); immOnLine

	| |- ?M = NotEquiDirectedInterPoint ?l1 ?l2 ?H => apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); immCollinear
	| |- NotEquiDirectedInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); immCollinear

	| |- ?M = FourPointsInterPoint ?l1 ?l2 ?H => apply (UniqueFourPointsInterPoint l1 l2 H M); immCollinear
	| |- FourPointsInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueFourPointsInterPoint l1 l2 H M); immCollinear

	| |- ?M = InterDiameterPoint ?l ?c ?H => apply (UniqueInterDiameterPoint l c H M); [immEquiOriented | immOnCircle]
	| |- InterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueInterDiameterPoint l c H M);  [immEquiOriented | immOnCircle]

	| |- ?M = SecondInterDiameterPoint ?l ?c ?H => apply (UniqueSecondInterDiameterPoint l c H M); [immEquiOriented | immOnCircle]
	| |- SecondInterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueSecondInterDiameterPoint l c H M);  [immEquiOriented | immOnCircle]

	| |- ?M = AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 => apply (UniqueAddSegmentPoint A B C D E H H0 M); [immEquiOriented | solveDistance]
	| |- AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 = ?M => apply sym_eq; apply (UniqueAddSegmentPoint A B C D E H H0 M); [immEquiOriented | solveDistance]

	| |- ?M = MarkSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueMarkSegmentPoint A B C D H M); [immClosedRay | solveDistance]
	| |- MarkSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueMarkSegmentPoint A B C D H M); [immClosedRay | solveDistance]

	| |- ?M = OppSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueOppSegmentPoint A B C D H M); [immSegment | solveDistance]
	| |- OppSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueOppSegmentPoint A B C D H M); [immSegment | solveDistance]

	| |- ?M = SymmetricPoint ?A ?B ?H => apply (UniqueSymmetricPoint A B H M); [immBetween | solveDistance]
	| |- SymmetricPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueSymmetricPoint A B H M); [immBetween | solveDistance]

	| |- ?M = PerpendicularPoint ?d1 ?d2 ?Hp => apply (UniquePerpendicularPoint M d1 d2 Hp); immOnLine
	| |- PerpendicularPoint ?d1 ?d2 ?Hp = ?M => apply sym_eq; apply (UniquePerpendicularPoint M d1 d2 Hp); immOnLine

	| |- ?A = LineA (Parallel ?d ?A ?H) => apply (LineAParallel d A H)
	| |- LineA (Parallel ?d ?A ?H) = ?A => apply sym_eq; apply (LineAParallel d A H)

	| H1 : IsAngle ?alpha, H2 : IsAngle ?beta |- ?alpha = ?beta => apply (EqAngle alpha beta H1 H2); solveDistance

	| |- Oo = MidPoint Uu uU DistinctUuuU => exact MidPointUuuUOo
	| |- Oo = MidPoint Uu uU ?H => rewrite (MidPointRefl Uu uU H DistinctUuuU); exact MidPointUuuUOo
	| |- MidPoint Uu uU DistinctUuuU = Oo => apply sym_eq; exact MidPointUuuUOo
	| |- MidPoint Uu uU ?H = Oo => apply sym_eq;  rewrite (MidPointRefl Uu uU H DistinctUuuU); exact MidPointUuuUOo
	| |- Oo = MidPoint uU Uu ?H =>  rewrite (MidPointSym uU Uu H DistinctUuuU); exact MidPointUuuUOo
	| |- MidPoint uU Uu ?H = Oo => apply sym_eq;  rewrite (MidPointSym uU Uu H DistinctUuuU); exact MidPointUuuUOo

	| |- MidPoint ?A ?B _  = MidPoint ?A ?B _ => apply MidPointRefl
	| |- MidPoint ?A ?B _  = MidPoint ?B ?A _ => apply MidPointSym
	| |- ?M = MidPoint ?A ?B ?H => apply (UniqueMidPoint A B H M); [immCollinear | solveDistance]
	| |- MidPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueMidPoint A B H M); [immCollinear | solveDistance]

	| |- ?A = ?B => match type of A with
			| Point => let H := fresh in (assert (H : Distance A B = Oo); [solveDistance | apply (NullDistanceEq A B H)])
			end

	| |- ?X = _ => unfold X; solveEq
	| |- _ = ?Y => unfold Y; solveEq
end.

Ltac orderAngle A B C D E F  := match goal with 
	| |- CongruentAngle A B C D E F => idtac
	| |- CongruentAngle C B A D E F =>  apply CongruentAngleRev1 
	| |- CongruentAngle A B C F E D => apply CongruentAngleRev2
	| |- CongruentAngle C B A F E D =>  apply CongruentAngleRev
 
	| |- CongruentAngle D E F A B C=>  apply CongruentAngleSym
	| |- CongruentAngle D E F C B A=>   apply CongruentAngleSym; apply CongruentAngleRev1 
	| |- CongruentAngle F E D A B C=>  apply CongruentAngleSym; apply CongruentAngleRev2
	| |- CongruentAngle F E D C B A=>   apply CongruentAngleSym; apply CongruentAngleRev
 end.

Ltac immRightAngle   := match goal with
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

Ltac immCongruentAngle := match goal with 
	| |- CongruentAngle ?A ?B ?C ?A ?B ?C => apply (CongruentAngleRefl A B C); try  immDistinct
	| |- CongruentAngle ?A ?B ?C ?C ?B ?A => apply (CongruentAnglePerm A B C); try  immDistinct

	|H : CongruentAngle ?A ?B ?C ?D ?E ?F  |- _ => orderAngle A B C D E F; exact H 

	|H : Angle ?A ?B ?C ?H1 ?H2  = Angle ?D ?E ?F ?H3 ?H4  |- _ => orderAngle A B C D E F; apply (CongruentEqAngle A B C D E F H1 H2 H3 H4 H)

	| H : RightAngle ?A ?B ?C  |- _ => orderAngle A B C Uu Oo Vv; exact H 
	| H : RightAngle ?A ?B ?C  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle
	| H : RightAngle ?C ?B ?A  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle
	| H : RightAngle ?D ?E ?F  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle
	| H : RightAngle ?F ?E ?D  |- CongruentAngle ?A ?B ?C ?D ?E ?F => apply (RightCongruentAngle A B C D E F); immRightAngle

	| H : OpenRay ?B ?A ?D |- CongruentAngle ?A ?B ?C ?D ?B ?C => apply (CongruentAngleSide1 A B C D); [immDistinct | immDistinct | immOpenRay]
	| H : OpenRay ?B ?C ?D |- CongruentAngle ?A ?B ?C ?A ?B ?D => apply (CongruentAngleSide2 A B C D); [immDistinct | immDistinct | immOpenRay]
	| H1 : OpenRay ?B ?A ?D, H2 : OpenRay ?B ?C ?E |- CongruentAngle ?A ?B ?C ?D ?B ?E => apply (CongruentAngleSides A B C D E); [immDistinct | immDistinct | immOpenRay | immOpenRay]

	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?A1 _ _ ?A2 _ => orderAngle  C1 A1 B1 C2 A2 B2; apply TCongruentAnglesA; [immDistinct | immDistinct | immDistinct | immDistinct | exact H]
	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?A2 _ _ ?A1 _ => orderAngle  C1 A1 B1 C2 A2 B2; apply TCongruentAnglesA; [immDistinct | immDistinct | immDistinct | immDistinct | exact H]

	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?B1 _ _ ?B2 _ => orderAngle  A1 B1 C1 A2 B2 C2; apply TCongruentAnglesB; [immDistinct | immDistinct | immDistinct | immDistinct | exact H]
	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?B2 _ _ ?B1 _ => orderAngle  A1 B1 C1 A2 B2 C2; apply TCongruentAnglesB; [immDistinct | immDistinct | immDistinct | immDistinct | exact H]

	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?C1 _ _ ?C2 _ => orderAngle  B1 C1 A1 B2 C2 A2; apply TCongruentAnglesC; [immDistinct | immDistinct | immDistinct | immDistinct | exact H]
	| H : TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) |- CongruentAngle _ ?C2 _ _ ?C1 _ => orderAngle  B1 C1 A1 B2 C2 A2; apply TCongruentAnglesC; [immDistinct | immDistinct | immDistinct | immDistinct | exact H]

	| H : Isosceles1 (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?C _ => orderAngle  A B C A C B; apply IsoscelesEqAngles1; [immDistinct | immDistinct | immDistinct | exact H]
	| H : Isosceles1 (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?B _ => orderAngle  A B C A C B; apply IsoscelesEqAngles1; [immDistinct | immDistinct | immDistinct | exact H]

	| H : Isosceles2 (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?A _ => orderAngle  B C A B A C; apply IsoscelesEqAngles2; [immDistinct | immDistinct | immDistinct | exact H]
	| H : Isosceles2 (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?C _ => orderAngle  B C A B A C; apply IsoscelesEqAngles2; [immDistinct | immDistinct | immDistinct | exact H]

	| H : Isosceles3 (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?B _ => orderAngle  C A B C B A; apply IsoscelesEqAngles3; [immDistinct | immDistinct | immDistinct | exact H]
	| H : Isosceles3 (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?A _ => orderAngle   C A B C B A; apply IsoscelesEqAngles3; [immDistinct | immDistinct | immDistinct | exact H]

	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?C _ => orderAngle  A B C A C B; apply IsoscelesEqAngles1; [immDistinct | immDistinct | immDistinct | exact (EquilateralIsosceles1 A B C H)]
	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?B _ => orderAngle  A B C A C B; apply IsoscelesEqAngles1; [immDistinct | immDistinct | immDistinct | exact (EquilateralIsosceles1 A B C H)]

	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?C _ _ ?A _ => orderAngle  B C A B A C; apply IsoscelesEqAngles2; [immDistinct | immDistinct | immDistinct | exact (EquilateralIsosceles2 A B C H)]
	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?C _ => orderAngle  B C A B A C; apply IsoscelesEqAngles2; [immDistinct | immDistinct | immDistinct | exact (EquilateralIsosceles2 A B C H)]

	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?A _ _ ?B _ => orderAngle  C A B C B A; apply IsoscelesEqAngles3; [immDistinct | immDistinct | immDistinct | exact (EquilateralIsosceles3 A B C H)]
	| H : Equilateral (Tr ?A ?B ?C) |- CongruentAngle _ ?B _ _ ?A _ => orderAngle   C A B C B A; apply IsoscelesEqAngles3; [immDistinct | immDistinct | immDistinct | exact (EquilateralIsosceles3 A B C H)]

	| H : OpposedAngles ?A ?B ?C ?D ?E |- CongruentAngle _ ?A _ _ ?A _ => orderAngle  B A C D A E; apply OpposedCongruentAngles; exact H

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?B ?B ?C ?D  => apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?D ?B ?C ?D  => apply CongruentAngleRev1; apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?B ?D ?C ?B  => apply CongruentAngleRev2; apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?D ?D ?C ?B  => apply CongruentAngleRev; apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?D ?D ?A ?B  => apply CongruentAngleSym; apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?D ?B ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?B ?D ?A ?B  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammDABeqBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?B ?B ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammDABeqBCD A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?C ?C ?D ?A  => apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?A ?C ?D ?A  => apply CongruentAngleRev1; apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?C ?A ?D ?C  => apply CongruentAngleRev2; apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?A ?A ?D ?C  => apply CongruentAngleRev; apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?A ?A ?B ?C  => apply CongruentAngleSym; apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?A ?C ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?C ?A ?B ?C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammABCeqCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?C ?C ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammABCeqCDA A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?C ?D ?C ?A  => apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?B ?D ?C ?A  => apply CongruentAngleRev1; apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?A ?C ?A ?C ?D  => apply CongruentAngleRev2; apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?B ?A ?C ?D  => apply CongruentAngleRev; apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?A ?B ?A ?C  => apply CongruentAngleSym; apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?C ?A ?C ?A ?B  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?D ?B ?A ?C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammBACeqDCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?D ?C ?A ?B  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammBACeqDCA A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?C ?B ?C ?A  => apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?D ?B ?C ?A  => apply CongruentAngleRev1; apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?A ?C ?A ?C ?B  => apply CongruentAngleRev2; apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?A ?D ?A ?C ?B  => apply CongruentAngleRev; apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?A ?D ?A ?C  => apply CongruentAngleSym; apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?C ?A ?C ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?B ?D ?A ?C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammDACeqBCA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?C ?B ?C ?A ?D  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammDACeqBCA A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?D ?C ?D ?B  => apply (ParallelogrammABDeqCDB A B C D H); immDistinct	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?A ?C ?D ?B  => apply CongruentAngleRev1; apply (ParallelogrammABDeqCDB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?B ?D ?B ?D ?C  => apply CongruentAngleRev2; apply (ParallelogrammABDeqCDB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?A ?B ?D ?C  => apply CongruentAngleRev; apply (ParallelogrammABDeqCDB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?B ?A ?B ?D  => apply CongruentAngleSym; apply (ParallelogrammABDeqCDB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?D ?B ?D ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammABDeqCDB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?C ?A ?B ?D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammABDeqCDB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?C ?D ?B ?A  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammABDeqCDB A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?B ?C ?B ?D  => apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?A ?C ?B ?D  => apply CongruentAngleRev1; apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?A ?D ?B ?D ?B ?C  => apply CongruentAngleRev2; apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?B ?D ?A ?D ?B ?C  => apply CongruentAngleRev; apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?D ?A ?D ?B  => apply CongruentAngleSym; apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?C ?B ?D ?B ?D ?A  => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?C ?A ?D ?B  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammADBeqCBD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- CongruentAngle ?D ?B ?C ?B ?D ?A  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammADBeqCBD A B C D H); immDistinct

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

Ltac immSupplement := match goal with
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
 
	| H : RightAngle ?A ?B ?C |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle
	| H : RightAngle ?C ?B ?A |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle
	| H : RightAngle ?D ?E ?F |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle
	| H : RightAngle ?F ?E ?D |- Supplement ?A ?B ?C ?D ?E ?F => apply RightRightSupplement; immRightAngle

	| H : Between ?B ?A ?D |- Supplement ?B ?A ?C ?C ?A ?D => apply BetweenSupplementAngles; [try immDistinct | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?B ?C ?A ?D => apply SupplementRev1; apply BetweenSupplementAngles; [try immDistinct | exact H]
	| H : Between ?B ?A ?D |- Supplement ?B ?A ?C ?D ?A ?C => apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?B ?D ?A ?C => apply SupplementRev1; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct | exact H]

	| H : Between ?B ?A ?D |- Supplement ?C ?A ?D ?B ?A ?C => apply SupplementSym; apply BetweenSupplementAngles; [try immDistinct | exact H]
	| H : Between ?B ?A ?D |- Supplement ?C ?A ?D ?C ?A ?B => apply SupplementSym; apply SupplementRev1; apply BetweenSupplementAngles; [try immDistinct | exact H]
	| H : Between ?B ?A ?D |- Supplement ?D ?A ?C ?B ?A ?C => apply SupplementSym; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct | exact H]
	| H : Between ?B ?A ?D |- Supplement ?D ?A ?C ?C ?A ?B => apply SupplementSym; apply SupplementRev1; apply SupplementRev2; apply BetweenSupplementAngles; [try immDistinct | exact H]

	| H : Parallelogramm ?A ?B ?C ?D  |- Supplement ?D ?A ?B ?A ?B ?C => apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?A ?B ?C =>  apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?C ?B ?A => apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?C ?B ?A =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?D ?A ?B => apply SupplementSym; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?B ?A ?D => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?D ?A ?B => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?B ?A ?D => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?B ?C ?D => apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?B ?C ?D =>  apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?B ?C ?D ?C ?B => apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?B ?A ?D ?C ?B =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?A ?B ?C => apply SupplementSym; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?C ?B ?A => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?A ?B ?C => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?C ?B ?A => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?C ?D ?A => apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?C ?D ?A =>  apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?C ?D ?A ?D ?C => apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?C ?B ?A ?D ?C =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?B ?C ?D => apply SupplementSym; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?D ?C ?B => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?B ?C ?D => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?D ?C ?B => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA A B C D H); immDistinct

	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?D ?A ?B => apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?D ?A ?B =>  apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?C ?D ?A ?B ?A ?D => apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?A ?D ?C ?B ?A ?D =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?C ?D ?A => apply SupplementSym; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?D ?A ?B ?A ?D ?C => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?C ?D ?A => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct
	| H : Parallelogramm ?A ?B ?C ?D |- Supplement ?B ?A ?D ?A ?D ?C => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB A B C D H); immDistinct

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

(* remplace les egalites d'angle par la relation : *)
Ltac eqToCongruent := 
(* dans les hypotheses *)
repeat match goal with

(* de congruence : *)
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Angle ?D ?E ?F ?Hed ?Hef  |- _ => let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C D E F Hba Hbc Hed Hef H)); clear H

(* de supplementarite : *)
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef)  |- _ => let Hyp := fresh in assert (Hyp := (EqAngleSupplement A B C D E F Hba Hbc Hed Hef H)); clear H
	| H : Supplementary (Angle ?D ?E ?F ?Hed ?Hef)  (IsAngleAngle ?D ?E ?F ?Hed ?Hef) = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (EqAngleSupplement A B C D E F Hba Hbc Hed Hef (sym_eq H))); clear H

(* d'angle nul : *)
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Uu  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc H)); clear H
	| H : Uu = Angle ?A ?B ?C ?Hba ?Hbc  |- _ => let Hyp := fresh in assert (Hyp := (NullEqAngle A B C Hba Hbc (sym_eq H))); clear H

(* d'angle plat : *)
	| H : Angle ?A ?B ?C ?Hba ?Hbc = uU  |- _ => let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc H)); clear H
	| H : uU = Angle ?A ?B ?C ?Hba ?Hbc  |- _ =>  let Hyp := fresh in assert (Hyp := (ElongatedEqAngle A B C Hba Hbc (sym_eq H))); clear H

(* d'angle droit : *)
	| H : Angle ?A ?B ?C ?Hba ?Hbc = Vv  |- _ => let Hyp := fresh in assert (Hyp := (AngleVvEqRight A B C Hba Hbc H)); clear H
	| H : Vv = Angle ?A ?B ?C ?Hba ?Hbc  |- _ =>  let Hyp := fresh in assert (Hyp := (AngleVvEqRight A B C Hba Hbc (sym_eq H))); clear H

(* d'angle defini en hypothese : *)
	| Ha : IsAngle ?alpha, H : Angle ?A ?B ?C ?Hba ?Hbc = ?alpha |- _ => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha Ha) Ha) in H;  let Hyp := fresh in assert (Hyp := (CongruentEqAngle A B C Uu Oo alpha Hba Hbc DistinctOoUu (IsAngleDistinctOo alpha Ha) H)); clear H
	| Ha : IsAngle ?alpha, H : ?alpha = Angle ?A ?B ?C ?Hba ?Hbc |- _ => rewrite <- (EqAnglePoint alpha DistinctOoUu (IsAngleDistinctOo alpha Ha) Ha) in H; let Hyp := fresh in assert (Hyp := (CongruentEqAngle Uu Oo alpha A B C DistinctOoUu (IsAngleDistinctOo alpha Ha) Hba Hbc H)); clear H

end; 
(* dans le but *)
match goal with
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

Ltac immNullAngle := match goal with 
	| H : NullAngle ?A ?B ?C |- NullAngle ?A ?B ?C => exact H
	| H : NullAngle ?A ?B ?C |- NullAngle ?C ?B ?A => apply (CongruentNullAngle A B C C B A); [exact H | apply CongruentAnglePerm; immDistinct]

	| |- NullAngle ?A ?B ?C => apply (OpenRayNullAngle B A C); [immDistinct | immOpenRay]
end.

Ltac immElongatedAngle := match goal with 
	| H : ElongatedAngle ?A ?B ?C |- ElongatedAngle ?A ?B ?C => exact H
	| H : ElongatedAngle ?A ?B ?C |- ElongatedAngle ?C ?B ?A => apply (CongruentElongatedAngle A B C C B A); [exact H | apply CongruentAnglePerm; immDistinct]

	| |- ElongatedAngle ?A ?B ?C => apply (BetweenElongatedAngle B A C);  immBetween
end.

Ltac immIsAngle := match goal with
	| H : IsAngle ?alpha |- IsAngle ?alpha => exact H

	| |- IsAngle Uu => apply IsAngleNullAngle
	| |- IsAngle uU => apply IsAngleElongatedAngle
	| |- IsAngle Vv => apply IsAngleVv

	| |- IsAngle (Angle _ _ _ _ _) =>  apply IsAngleAngle
	| |- IsAngle (Supplementary _ _ ) =>  apply IsAngleSupplementary

	| |- IsAngle _ => unfold IsAngle; simplCircle; split; [immOnCircle | immNotClockwise]
end.

Ltac solveAngle := match goal with 
	| |- Angle _ _ _ _ _ = Angle _ _ _ _ _ => apply EqCongruentAngle; immCongruentAngle

	| |- Angle _ _ _ _ _ = Supplementary  _ _ => apply SupplementSupplementary; immSupplement
	| |- Supplementary  _ _ = Angle _ _ _ _ _  => apply sym_eq; apply SupplementSupplementary; immSupplement

	| |- Angle ?A ?B ?C _ _ = Uu => eqToCongruent; immNullAngle
	| |- Uu = Angle ?A ?B ?C _ _ => eqToCongruent; immNullAngle

	| |- Angle ?A ?B ?C _ _ = uU => eqToCongruent; immElongatedAngle
	| |- uU = Angle ?A ?B ?C _ _ => eqToCongruent; immElongatedAngle

	| |- Angle ?A ?B ?C _ _ = Vv => eqToCongruent; immRightAngle
	| |- Vv = Angle ?A ?B ?C _ _ => eqToCongruent; immRightAngle

	| |- Angle Uu Oo ?M _ _ = ?M => apply EqAnglePoint; immIsAngle
	| |- ?M = Angle Uu Oo ?M _ _  => apply sym_eq; apply EqAnglePoint; immIsAngle
	| |- Angle ?M Oo Uu ?H1 ?H2 = ?M => rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2));  apply EqAnglePoint; immIsAngle
	| |- ?M = Angle ?M Oo Uu ?H1 ?H2  => apply sym_eq;  rewrite (EqCongruentAngle M Oo Uu Uu Oo M H1 H2 H2 H1 (CongruentAnglePerm M Oo Uu H1 H2)); apply EqAnglePoint; immIsAngle
end.

Ltac solveSupplementary :=  match goal with
	| |- Supplementary _ _ = Supplementary _ _ => apply SupplementaryEqAngles; solveSupplementary
	| |- Supplementary (Supplementary _ _) _ = _ => rewrite SupplementarySupplementary; solveSupplementary
	| |- _ = Supplementary (Supplementary _ _) _ => rewrite SupplementarySupplementary; solveSupplementary

	| |- Supplementary Uu _ = _ => rewrite SupplementaryNullAngle; solveSupplementary	| |- _ = Supplementary Uu _  => rewrite SupplementaryNullAngle; solveSupplementary	| |- Supplementary uU _ = _ => rewrite SupplementaryElongatedAngle; solveSupplementary	| |- _ = Supplementary uU _  => rewrite SupplementaryElongatedAngle; solveSupplementary

	| |- Supplementary Vv _ = _ => rewrite SupplementaryRightAngle; solveAngle
	| |- _ = Supplementary Vv _  => rewrite SupplementaryRightAngle; solveAngle	

	| |- _ = _ => solveAngle
end.

Ltac immNotNullAngle := match goal with 
	| H : ElongatedAngle ?A ?B ?C |- ~NullAngle ?A ?B ?C => apply (ElongatedAngleNotNullAngle A B C H)
	| H : ElongatedAngle ?A ?B ?C |- ~NullAngle ?C ?B ?A => apply (ElongatedAngleNotNullAngle C B A); immElongatedAngle
	| H : RightAngle ?A ?B ?C |- ~NullAngle ?A ?B ?C => apply (RightAngleNotNullAngle A B C H)
	| H : RightAngle ?A ?B ?C |- ~NullAngle ?C ?B ?A => apply (RightAngleNotNullAngle C B A); immRightAngle
end.

Ltac immNotElongatedAngle := match goal with 
	| H : NullAngle ?A ?B ?C |- ~ElongatedAngle ?A ?B ?C => apply (NullAngleNotElongatedAngle A B C H)
	| H : NullAngle ?A ?B ?C |- ~ElongatedAngle ?C ?B ?A => apply (NullAngleNotElongatedAngle C B A); immNullAngle
	| H : RightAngle ?A ?B ?C |- ~ElongatedAngle ?A ?B ?C => apply (RightAngleNotElongatedAngle A B C H)
	| H : RightAngle ?A ?B ?C |- ~ElongatedAngle ?C ?B ?A => apply (RightAngleNotElongatedAngle C B A); immRightAngle
end.

Ltac immNotRightAngle := match goal with 
	| H : NullAngle ?A ?B ?C |- ~RightAngle ?A ?B ?C => apply (NullAngleNotRightAngle A B C H)
	| H : NullAngle ?A ?B ?C |- ~RightAngle ?C ?B ?A => apply (NullAngleNotRightAngle C B A); immNullAngle
	| H : ElongatedAngle ?A ?B ?C |- ~RightAngle ?A ?B ?C => apply (ElongatedAngleNotRightAngle A B C H)
	| H : ElongatedAngle ?A ?B ?C |- ~RightAngle ?C ?B ?A => apply (ElongatedAngleNotRightAngle C B A); immElongatedAngle
end.

Ltac immNotCollinear := match goal with
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?A ?B ?C => exact H	
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?A ?C ?B => intro; elim H; immCollinear
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?B ?A ?C =>  intro; elim H; immCollinear
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?B ?C ?A =>  intro; elim H; immCollinear
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?C ?A ?B =>  intro; elim H; immCollinear
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?C ?B ?A =>  intro; elim H; immCollinear

	| H : RightAngle ?A ?B ?C |- ~Collinear ?A ?B ?C => apply (RightAngleNotCollinear A B C H)
	| H : RightAngle ?A ?B ?C |- ~Collinear ?A ?C ?B => let Hyp := fresh in (assert (Hyp := RightAngleNotCollinear A B C H);  contrapose Hyp; immCollinear)
	| H : RightAngle ?A ?B ?C |- ~Collinear ?B ?A ?C =>  let Hyp := fresh in (assert (Hyp := RightAngleNotCollinear A B C H); contrapose Hyp; immCollinear)
	| H : RightAngle ?A ?B ?C |- ~Collinear ?B ?C ?A =>  let Hyp := fresh in (assert (Hyp := RightAngleNotCollinear A B C H); contrapose Hyp; immCollinear)
	| H : RightAngle ?A ?B ?C |- ~Collinear ?C ?A ?B =>  let Hyp := fresh in (assert (Hyp := RightAngleNotCollinear A B C H); contrapose Hyp; immCollinear)
	| H : RightAngle ?A ?B ?C |- ~Collinear ?C ?B ?A =>  let Hyp := fresh in (assert (Hyp := RightAngleNotCollinear A B C H); contrapose Hyp; immCollinear)

	|  |- ~Collinear ?A ?B ?C => apply ClockwiseABCNotCollinear; immClockwise
	|  |- ~Collinear ?A ?B ?C => apply ClockwiseBACNotCollinear; immClockwise
end.

Ltac immEquiDirected := match goal with
	| H : EquiDirected ?A ?B ?C ?D |- EquiDirected ?A ?B ?C ?D => exact H
	| H : EquiDirected ?B ?A ?C ?D |- EquiDirected ?A ?B ?C ?D => apply EquiDirectedPermutAB; exact  H
	| H : EquiDirected ?A ?B ?D ?C |- EquiDirected ?A ?B ?C ?D => apply EquiDirectedPermutCD; exact  H
	| H : EquiDirected ?B ?A ?D ?C |- EquiDirected ?A ?B ?C ?D => apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; exact  H

	| H : EquiDirected ?A ?B ?C ?D |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; exact H
	| H : EquiDirected ?B ?A ?C ?D |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutAB; exact  H
	| H : EquiDirected ?A ?B ?D ?C |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutCD; exact  H
	| H : EquiDirected ?B ?A ?D ?C |- EquiDirected ?C ?D ?A ?B => apply EquiDirectedSym; apply EquiDirectedPermutCD; apply  EquiDirectedPermutAB; exact  H

	| |-  EquiDirected ?A ?B ?C ?A   => apply CollinearEquiDirected; immCollinear
	| |-  EquiDirected ?B ?A ?C ?A   => apply EquiDirectedPermutAB; apply CollinearEquiDirected; immCollinear
	| |-  EquiDirected ?A ?B ?A  ?C  => apply EquiDirectedPermutCD; apply CollinearEquiDirected; immCollinear
	| |-  EquiDirected ?B ?A ?A  ?C  => apply EquiDirectedSym; apply CollinearEquiDirected; immCollinear

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

	| Hp : StrictParallelogramm _ _ _ _ |-  EquiDirected ?A ?B ?C ?D => inversion_clear Hp; immEquiDirected
end.

Ltac immNotEquiDirected := match goal with
	| H : ~EquiDirected ?A ?B ?C ?D |- ~EquiDirected ?A ?B ?C ?D => exact H
	| H : ~EquiDirected _ _ _ _  |- ~EquiDirected _ _ _ _  => contrapose H; immEquiDirected
	| H : EquiDirected _ _ _ _  -> False |- ~EquiDirected _ _ _ _  => contrapose H; immEquiDirected
	| H : ~Collinear _ _ _  |- ~EquiDirected _ _ _ _ => contrapose H; immCollinear
	| H : Collinear _ _ _  -> False |- ~EquiDirected _ _ _ _ => contrapose H; immCollinear

	|  |- ~EquiDirected _ _ _ _ => apply FourPointsSecantLine; [immClockwise | immNotClockwise]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise | immNotClockwise]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedPermutCD; apply FourPointsSecantLine; [immClockwise | immNotClockwise]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedPermutCD; apply  NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise | immNotClockwise]

	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply FourPointsSecantLine; [immClockwise | immNotClockwise]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise | immNotClockwise]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply NotEquiDirectedPermutCD; apply FourPointsSecantLine; [immClockwise | immNotClockwise]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply NotEquiDirectedPermutCD; apply  NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise | immNotClockwise]
end.

Ltac immDistanceLe := match goal with
	| |- DistanceLe Oo _ => apply DistanceLeOo
	| |- DistanceLe ?A ?A => apply DistanceLeRefl

	| |- DistanceLe (Distance ?A ?B) (Distance ?A ?C) => apply SegmentDistanceLe; immSegment
	| |- DistanceLe (Distance ?B ?A) (Distance ?A ?C) => rewrite (DistanceSym B A); apply SegmentDistanceLe; immSegment
	| |- DistanceLe (Distance ?A ?B) (Distance ?C ?A) =>  rewrite (DistanceSym C A); apply SegmentDistanceLe; immSegment
	| |- DistanceLe (Distance ?B ?A) (Distance ?C ?A) => rewrite (DistanceSym B A);  rewrite (DistanceSym C A); apply SegmentDistanceLe; immSegment

	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus ?A ?C) => apply LeftRegularDistanceLe; immDistanceLe
	| |- DistanceLe (DistancePlus ?B ?A) (DistancePlus ?A ?C) => rewrite (DistancePlusCommut B A); apply LeftRegularDistanceLe; immDistanceLe
	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus ?C ?A) =>  rewrite (DistancePlusCommut C A); apply LeftRegularDistanceLe; immDistanceLe
	| |- DistanceLe (DistancePlus ?B ?A) (DistancePlus ?C ?A) => rewrite (DistancePlusCommut B A);  rewrite (DistancePlusCommut C A); apply LeftRegularDistanceLe; immDistanceLe

	| |- DistanceLe (Distance ?A ?C) (DistancePlus (Distance ?A ?B) (Distance ?B ?C)) => apply TriangularInequalityABBCAC
	| |- DistanceLe (Distance ?A ?C) (DistancePlus (Distance ?B ?A) (Distance ?B ?C)) => apply TriangularInequalityBABCAC
	| |- DistanceLe (Distance ?A ?C) (DistancePlus (Distance ?A ?B) (Distance ?C ?B)) =>  apply TriangularInequalityABCBAC
	| |- DistanceLe (Distance ?A ?C) (DistancePlus (Distance ?B ?A) (Distance ?C ?B)) =>   apply TriangularInequalityBACBAC
	| |- DistanceLe (Distance ?C ?A) (DistancePlus (Distance ?A ?B) (Distance ?B ?C)) => apply TriangularInequalityABBCCA
	| |- DistanceLe (Distance ?C ?A) (DistancePlus (Distance ?B ?A) (Distance ?B ?C)) =>  apply TriangularInequalityBABCCA
	| |- DistanceLe (Distance ?C ?A) (DistancePlus (Distance ?A ?B) (Distance ?C ?B)) => apply TriangularInequalityABCBCA
	| |- DistanceLe (Distance ?C ?A) (DistancePlus (Distance ?B ?A) (Distance ?C ?B)) => apply TriangularInequalityBACBCA

	| |- DistanceLe (Distance ?A ?B) (DistancePlus (Distance ?A ?B) _) => apply DistanceLeDistancePlusDistance
	| |- DistanceLe (Distance ?A ?B) (DistancePlus _ (Distance ?A ?B)) => rewrite DistancePlusCommut; apply DistanceLeDistancePlusDistance
	| |- DistanceLe (Distance ?A ?B) (DistancePlus (Distance ?B ?A) _) => rewrite (DistanceSym B A); apply DistanceLeDistancePlusDistance
	| |- DistanceLe (Distance ?A ?B) (DistancePlus _ (Distance ?B ?A)) => rewrite (DistanceSym B A); rewrite DistancePlusCommut; apply DistanceLeDistancePlusDistance

	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus (DistancePlus ?A ?B) _) => apply DistanceLeDistancePlusDistancePlus
	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus _ (DistancePlus ?A ?B)) => rewrite DistancePlusCommut; apply DistanceLeDistancePlusDistancePlus
	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus (DistancePlus ?B ?A) _) => rewrite (DistancePlusCommut B A); apply DistanceLeDistancePlusDistancePlus
	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus _ (DistancePlus ?B ?A)) => rewrite (DistancePlusCommut B A); rewrite DistancePlusCommut; apply DistanceLeDistancePlusDistancePlus

	| |- DistanceLe ?A (DistancePlus ?A _) => apply DistanceLeDistancePlus; immIsDistance A
	| |- DistanceLe ?A (DistancePlus _ ?A) => rewrite DistancePlusCommut; apply DistanceLeDistancePlus; immIsDistance A

	| H : Segment ?A ?B ?C |- DistanceLe (Distance ?A ?C) (Distance ?A ?B) => apply (SegmentDistanceLe A B C H)
	| H : Segment ?A ?B ?C |- DistanceLe (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C H)
	| H : Segment ?A ?B ?C |- DistanceLe (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (SegmentDistanceLe A B C H)
	| H : Segment ?A ?B ?C |- DistanceLe (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C H)

	| H : Segment ?B ?A ?C |- DistanceLe (Distance ?A ?C) (Distance ?A ?B) => apply (SegmentDistanceLe A B C (SegmentSym B A C H))
	| H : Segment ?B ?A ?C |- DistanceLe (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (SegmentSym B A C H))
	| H : Segment ?B ?A ?C |- DistanceLe (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (SegmentDistanceLe A B C (SegmentSym B A C H))
	| H : Segment ?B ?A ?C |- DistanceLe (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (SegmentSym B A C H))

	| H : Between ?A ?C ?B |- DistanceLe (Distance ?A ?C) (Distance ?A ?B) => apply (SegmentDistanceLe A B C (BetweenSegment A C B H))
	| H : Between ?A ?C ?B |- DistanceLe (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (BetweenSegment A C B H))
	| H : Between ?A ?C ?B |- DistanceLe (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (SegmentDistanceLe A B C (BetweenSegment A C B H))
	| H : Between ?A ?C ?B |- DistanceLe (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (BetweenSegment A C B H))

	| H : Between ?B ?C ?A |- DistanceLe (Distance ?A ?C) (Distance ?A ?B) => apply (SegmentDistanceLe A B C (SegmentSym B A C (BetweenSegment B C A H)))
	| H : Between ?B ?C ?A |- DistanceLe (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (SegmentSym B A C (BetweenSegment B C A H)))
	| H : Between ?B ?C ?A |- DistanceLe (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (SegmentDistanceLe A B C (SegmentSym B A C (BetweenSegment B C A H)))
	| H : Between ?B ?C ?A |- DistanceLe (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (SegmentSym B A C (BetweenSegment B C A H)))

	| H : EquiOriented ?A ?C ?C ?B |- DistanceLe (Distance ?A ?C) (Distance ?A ?B) => apply (SegmentDistanceLe A B C (EquiOrientedSegment A C B H))
	| H : EquiOriented ?A ?C ?C ?B |- DistanceLe (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (EquiOrientedSegment A C B H))
	| H : EquiOriented ?A ?C ?C ?B |- DistanceLe (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (SegmentDistanceLe A B C (EquiOrientedSegment A C B H))
	| H : EquiOriented ?A ?C ?C ?B |- DistanceLe (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (EquiOrientedSegment A C B H))

	| H : EquiOriented ?B ?C ?C ?A |- DistanceLe (Distance ?A ?C) (Distance ?A ?B) => apply (SegmentDistanceLe A B C (SegmentSym B A C (EquiOrientedSegment B C A H)))
	| H : EquiOriented ?B ?C ?C ?A |- DistanceLe (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (SegmentSym B A C (EquiOrientedSegment B C A H)))
	| H : EquiOriented ?B ?C ?C ?A |- DistanceLe (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (SegmentDistanceLe A B C (SegmentSym B A C (EquiOrientedSegment B C A H)))
	| H : EquiOriented ?B ?C ?C ?A |- DistanceLe (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (SegmentDistanceLe A B C (SegmentSym B A C (EquiOrientedSegment B C A H)))

	| |- DistanceLe _ _ => unfold DistanceLe; immSegment
end.

Ltac immDistanceLt := match goal with
	| |- DistanceLt ?A (DistancePlus ?A _) => apply DistanceLtDistancePlus; [immDistinct | immIsDistance]
	| |- DistanceLt ?A (DistancePlus _ ?A) => rewrite DistancePlusCommut; apply DistanceLtDistancePlus; [immDistinct | immIsDistance]

	| H : Between ?A ?C ?B |- DistanceLt (Distance ?A ?C) (Distance ?A ?B) => apply (BetweenDistanceLt A C B H)
	| H : Between ?A ?C ?B |- DistanceLt (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B H)
	| H : Between ?A ?C ?B |- DistanceLt (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (BetweenDistanceLt A C B H)
	| H : Between ?A ?C ?B |- DistanceLt (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B H)

	| H : Between ?B ?C ?A |- DistanceLt (Distance ?A ?C) (Distance ?A ?B) => apply (BetweenDistanceLt A C B (BetweenSym B C A H))
	| H : Between ?B ?C ?A |- DistanceLt (Distance ?C ?A) (Distance ?A ?B) => rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B (BetweenSym B C A H))
	| H : Between ?B ?C ?A |- DistanceLt (Distance ?A ?C) (Distance ?B ?A) => rewrite (DistanceSym B A); apply (BetweenDistanceLt A C B (BetweenSym B C A H))
	| H : Between ?B ?C ?A |- DistanceLt (Distance ?C ?A) (Distance ?B ?A) => rewrite (DistanceSym B A); rewrite (DistanceSym C A); apply (BetweenDistanceLt A C B (BetweenSym B C A H))

	| |- DistanceLt _ _ => split; [immDistanceLe | immDistinct]
end.

Ltac immTriangularInequality := match goal with
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

Ltac immTriangleSpec := match goal with
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

Ltac immDiameter := match goal with
	| |- Diameter lineOoUu uCircle => apply DiameterlineOoUuuCircle
	| |- _ => simplCircle; immCollinear
end.

Ltac immTStrict := match goal with 
	| H: TStrict ?t |- TStrict ?t => exact H
	| |- TStrict (Tr ?A ?B ?C) => (right; immClockwise) || (left; immClockwise)
	| |- TStrict ?t => unfold t;  (right; immClockwise) || (left; immClockwise)
end.

(* le triangle est isocele en son premier sommet *)

Ltac immIsosceles1 := match goal with
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?A ?B ?C) => exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?C ?A ?B) => apply Isosceles31; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?C ?B ?A) => apply Isosceles1Sym; apply Isosceles31; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?B ?C ?A) => apply Isosceles31;  apply Isosceles23; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles1 (Tr ?B ?A ?C) => apply Isosceles1Sym; apply Isosceles31;  apply Isosceles23; exact H

	| H : Distance ?A ?B = Distance ?A ?C |-  Isosceles1 (Tr ?A ?B ?C) => simpl; exact H
	| H : Distance ?B ?A = Distance ?A ?C |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?A ?B = Distance ?C ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?B ?A = Distance ?C ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?A ?C = Distance ?A ?B |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?C ?A = Distance ?A ?B |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?A ?C = Distance ?B ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?C ?A = Distance ?B ?A |-  Isosceles1 (Tr ?A ?B ?C) => simpl; solveDistance 

	| H : CongruentAngle ?A ?B ?C  ?A ?C ?B   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?B ?A  ?A ?C ?B   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?A ?B ?C  ?B ?C ?A   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?B ?A  ?B ?C ?A   |-  Isosceles1 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?A ?B ?C   ?A ?C ?B  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?B ?A ?A ?C ?B  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?A ?B ?C  ?B ?C ?A  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?B ?A   ?B ?C ?A  |-  Isosceles1 (Tr ?A ?C ?B) => apply Isosceles1Sym; apply (EqAnglesIsosceles1 A B C); [immNotCollinear | solveAngle] 
end.

(* le triangle est isocele en son deuxieme sommet *)

Ltac immIsosceles2 := match goal with
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?A ?B ?C) => exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?C ?A ?B) => apply Isosceles12; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?C ?B ?A) => apply Isosceles2Sym; apply Isosceles12; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?B ?C ?A) => apply Isosceles12;  apply Isosceles31; exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles2 (Tr ?B ?A ?C) => apply Isosceles2Sym; apply Isosceles12;  apply Isosceles31; exact H

	| H : Distance ?B ?C = Distance ?B ?A |-  Isosceles2 (Tr ?A ?B ?C) => simpl; exact H
	| H : Distance ?C ?B = Distance ?B ?A |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?B ?C = Distance ?A ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?C ?B = Distance ?A ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?B ?A = Distance ?B ?C |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?A ?B = Distance ?B ?C |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?B ?A = Distance ?C ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?A ?B = Distance ?C ?B |-  Isosceles2 (Tr ?A ?B ?C) => simpl; solveDistance 

	| H : CongruentAngle ?B ?C ?A ?B ?A ?C  |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C  ); [immNotCollinear | solveAngle]  
	| H : CongruentAngle ?A ?C ?B ?B ?A ?C   |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?B ?C ?A ?C ?A ?B  |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?A ?C ?B  ?C ?A ?B  |-  Isosceles2 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?B ?C ?A ?B ?A ?C |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?A ?C ?B  ?B ?A ?C  |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?B ?C ?A  ?C ?A ?B  |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?A ?C ?B  ?C ?A ?B   |-  Isosceles2 (Tr ?A ?C ?B) => apply Isosceles2Sym; apply (EqAnglesIsosceles2 A B C ); [immNotCollinear | solveAngle] 
end.

(* le triangle est isocele en son troisieme sommet *)

Ltac immIsosceles3 := match goal with
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?A ?B ?C) => exact H
	| H : Isosceles3 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?C ?A ?B) => apply Isosceles23; exact H
	| H : Isosceles2 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?C ?B ?A) => apply Isosceles3Sym; apply Isosceles23; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?B ?C ?A) => apply Isosceles23;  apply Isosceles12; exact H
	| H : Isosceles1 (Tr ?A ?B ?C)  |- Isosceles3 (Tr ?B ?A ?C) => apply Isosceles3Sym; apply Isosceles23;  apply Isosceles12; exact H

	| H : Distance ?C ?A = Distance ?C ?B |-  Isosceles3 (Tr ?A ?B ?C) => simpl; exact H
	| H : Distance ?A ?C = Distance ?C ?B |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?C ?A = Distance ?B ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?A ?C = Distance ?B ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?C ?B = Distance ?C ?A |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?B ?C = Distance ?C ?A |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance
	| H : Distance ?C ?B = Distance ?A ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance 
	| H : Distance ?B ?C = Distance ?A ?C |-  Isosceles3 (Tr ?A ?B ?C) => simpl; solveDistance 

	| H : CongruentAngle ?C ?A ?B ?C ?B ?A  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle]  
	| H : CongruentAngle ?B ?A ?C  ?C ?B ?A  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?A ?B ?A ?B ?C  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?B ?A ?C  ?A ?B ?C  |-  Isosceles3 (Tr ?A ?B ?C) => apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?A ?B  ?C ?B ?A  |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?B ?A ?C  ?C ?B ?A  |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?C ?A ?B  ?A ?B ?C  |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle] 
	| H : CongruentAngle ?B ?A ?C ?A ?B ?C   |-  Isosceles3 (Tr ?A ?C ?B) => apply Isosceles3Sym; apply (EqAnglesIsosceles3 A B C ); [immNotCollinear | solveAngle] 
end.

(* le triangle est equilateral *)

Ltac immEquilateralBase := 
match goal with
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?A ?B ?C) => exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?A ?C ?B) => apply EquilateralSym; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?C ?A ?B) => do 2 apply EquilateralPerm; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?C ?B ?A) => apply EquilateralSym; do 2 apply EquilateralPerm; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?B ?C ?A) => apply EquilateralPerm; exact H
	| H : Equilateral (Tr ?A ?B ?C)  |- Equilateral (Tr ?B ?A ?C) => apply EquilateralSym; apply EquilateralPerm; exact H

	| |- Equilateral (Tr ?A ?B ?C) => solve 
		[ apply Isosceles12Equilateral; [immIsosceles1 | immIsosceles2] |
		 apply Isosceles23Equilateral; [immIsosceles2 | immIsosceles3] |
		 apply Isosceles31Equilateral; [immIsosceles3 | immIsosceles1] ]
end.

Ltac immEquilateral := immEquilateral || 
match goal with
	| |- context [(MidLine ?A ?B ?H)] => let Hyp1 := fresh in let Hyp2 := fresh in (
		assert (Hyp1 := EquilateralAMidLineAB A B H);
		assert (Hyp2 := EquilateralBMidLineBA A B H);
		immEquilateralBase)
end.

(* deux triangles sont congruents si leurs trois cotes respectifs sont de longueurs egales *)

Ltac usingSSS := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply SSSTCongruent
	| |- TCongruent ?t1 _ => unfold t1; usingSSS
	| |- TCongruent _ ?t2 => unfold t2; usingSSS
end.

(* deux triangles sont congruents si leurs deuxiemes sommets respectifs ont  angle egal et cotes adjascents de longueurs egales *)

Ltac usingSASb := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply (SASTCongruent A1 B1 C1 A2 B2 C2)
	| |- TCongruent ?t1 _ => unfold t1; usingSASb
	| |- TCongruent _ ?t2 => unfold t2; usingSASb
end.

(* deux triangles sont congruents si leurs premiers sommets respectifs ont  angle egal et cotes adjascents de longueurs egales *)

Ltac usingSASa := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply TCongruentPerm; apply (SASTCongruent  C1 A1 B1 C2 A2 B2)
	| |- TCongruent ?t1 _ => unfold t1; usingSASa
	| |- TCongruent _ ?t2 => unfold t2; usingSASa
end.

(* deux triangles sont congruents si leurs troisiemes sommets respectifs ont  angle egal et cotes adjascents de longueurs egales *)

Ltac usingSASc := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => do 2 apply TCongruentPerm; apply (SASTCongruent B1 C1 A1 B2 C2 A2)
	| |- TCongruent ?t1 _ => unfold t1; usingSASc
	| |- TCongruent _ ?t2 => unfold t2; usingSASc
end.

(* deux triangles sont congruents si leurs troisiemes cotes respectifs sont de longueurs egales et leurs angles adjascents respectifs egaux *)

Ltac usingASAca := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) => apply (ASATCongruent A1 B1 C1 A2 B2 C2)
	| |- TCongruent ?t1 _ => unfold t1; usingASAca
	| |- TCongruent _ ?t2 => unfold t2; usingASAca
end.

(* deux triangles sont congruents si leurs deuxiemes cotes respectifs sont de longueurs egales et leurs angles adjascents respectifs egaux *)

Ltac usingASAbc := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) =>  apply TCongruentPerm; apply (ASATCongruent  C1 A1 B1 C2 A2 B2)
	| |- TCongruent ?t1 _ => unfold t1; usingASAbc
	| |- TCongruent _ ?t2 => unfold t2; usingASAbc
end.

(* deux triangles sont congruents si leurs premiers cotes respectifs sont de longueurs egales et leurs angles adjascents respectifs egaux *)

Ltac usingASAab := match goal with
	| |- TCongruent (Tr ?A1 ?B1 ?C1) (Tr ?A2 ?B2 ?C2) =>  do 2 apply TCongruentPerm;apply (ASATCongruent B1 C1 A1 B2 C2 A2)
	| |- TCongruent ?t1 _ => unfold t1; usingASAab
	| |- TCongruent _ ?t2 => unfold t2; usingASAab
end.

Ltac immTCongruentBase := match goal with
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

	| |- TCongruent ?t1 _ => unfold t1; immTCongruentBase
	| |- TCongruent _ ?t2 => unfold t2; immTCongruentBase
end.

(* Les deux triangles sont congruents *)

Ltac immTCongruent := immTCongruentBase || match goal with
	| |- context [(MidLine ?A ?B ?Hab)] => let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in let Hyp4 := fresh in let Hyp5 := fresh in
 		(assert (Hyp1 := (TCongruentMidLineAMidLineB A B Hab));
		assert (Hyp2 := (TCongruentAIA'BIA' A B Hab));
		assert (Hyp3 := (TCongruentAIB'BIB' A B Hab));
		assert (Hyp4 := (TCongruentAIA'AIB' A B Hab));
		assert (Hyp5 := (TCongruentBIA'BIB' A B Hab)));
		immTCongruentBase

	| |- context [(PCenter ?A ?B ?C ?D ?Hp)] => let Hyp1 := fresh in let Hyp2 := fresh in  		(assert (Hyp1 := ParallelogrammTCongruentAKBCKD A B C D Hp);
		assert (Hyp2 := ParallelogrammTCongruentBKCDKA A B C D Hp));
		immTCongruentBase

	| |- context [(SPCenter ?A ?B ?C ?D ?Hsp)] => DestructSP11 Hsp; match goal with 
		| |- context [(PCenter ?A ?B ?C ?D ?Hp)] => let Hyp1 := fresh in let Hyp2 := fresh in  			(assert (Hyp1 := ParallelogrammTCongruentAKBCKD A B C D Hp);
			assert (Hyp2 := ParallelogrammTCongruentBKCDKA A B C D Hp));
			immTCongruentBase
		end

	| Hp : Parallelogramm ?A ?B ?C ?D |- _ => let Hyp1 := fresh in let Hyp2 := fresh in  		(assert (Hyp1 := ParallelogrammTCongruentABCCDA A B C D Hp);
		assert (Hyp2 := ParallelogrammTCongruentBCDDAB A B C D Hp));
		immTCongruentBase

	| H : StrictParallelogramm ?A ?B ?C ?D |- _ => DestructSP11 H; match goal with 
		| Hp : Parallelogramm ?A ?B ?C ?D |- _ => let Hyp1 := fresh in let Hyp2 := fresh in  			(assert (Hyp1 := ParallelogrammTCongruentABCCDA A B C D Hp);
			assert (Hyp2 := ParallelogrammTCongruentBCDDAB A B C D Hp));
			immTCongruentBase
		end	

	| _ => solve [usingSSS; solveDistance
				| usingSASa; [solveDistance | solveDistance | immCongruentAngle]
				| usingSASb; [solveDistance | solveDistance | immCongruentAngle] 
				| usingSASc; [solveDistance | solveDistance | immCongruentAngle]
				| usingASAab; [immNotCollinear | immCongruentAngle | immCongruentAngle | solveDistance] 
				| usingASAbc; [immNotCollinear | immCongruentAngle | immCongruentAngle | solveDistance] 
				| usingASAca; [immNotCollinear | immCongruentAngle | immCongruentAngle | solveDistance] ]
end.

Ltac immParallelogramm := match goal with 
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
	| H : MidPoint ?C ?A ?Hca = MidPoint ?B ?D ?Hbd |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) Hbd); rewrite <- H; solveEq
	| H : MidPoint ?A ?C ?Hac = MidPoint ?D ?B ?Hdb |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac (sym_not_eq Hdb)); rewrite H; solveEq
	| H : MidPoint ?C ?A ?Hca = MidPoint ?D ?B ?Hdb |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) (sym_not_eq Hdb)); replace (MidPoint A C (sym_not_eq Hca)) with (MidPoint C A Hca); [rewrite H; solveEq | solveEq]

	| H : MidPoint ?B ?D ?Hbd = MidPoint ?A ?C ?Hac |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac Hbd (sym_eq H))
	| H : MidPoint ?B ?D ?Hbd = MidPoint ?C ?A ?Hca |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) Hbd); rewrite H; solveEq
	| H : MidPoint ?D ?B ?Hdb = MidPoint ?A ?C ?Hac |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D Hac (sym_not_eq Hdb)); rewrite <- H; solveEq
	| H : MidPoint ?D ?B ?Hdb = MidPoint ?C ?A ?Hca |- Parallelogramm ?A ?B ?C ?D => apply (Pllgm A B C D (sym_not_eq Hca) (sym_not_eq Hdb)); replace (MidPoint A C (sym_not_eq Hca)) with (MidPoint C A Hca); [rewrite <- H; solveEq | solveEq]
end.

Ltac immStrictParallelogramm := match goal with 
	|  |- StrictParallelogramm ?A ?B ?C ?D  => apply SPDef; [immParallelogramm | immClockwise]

	| H : StrictParallelogramm ?B ?C ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => do 3 apply StrictParallelogrammPerm; exact H
	| H : StrictParallelogramm ?C ?D ?A ?B |- StrictParallelogramm ?A ?B ?C ?D  => do 2 apply StrictParallelogrammPerm; exact H
	| H : StrictParallelogramm ?D ?A ?B ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply StrictParallelogrammPerm; exact H

	| H : Clockwise ?B ?C ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseBCDStrictParallelogramm;  [immParallelogramm | immClockwise]
	| H : Clockwise ?C ?D ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseBCDStrictParallelogramm;  [immParallelogramm | immClockwise]
	| H : Clockwise ?D ?B ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseBCDStrictParallelogramm;  [immParallelogramm | immClockwise]

	| H : Clockwise ?A ?C ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseCDAStrictParallelogramm; [immParallelogramm | immClockwise]
	| H : Clockwise ?C ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseCDAStrictParallelogramm; [immParallelogramm | immClockwise]
	| H : Clockwise ?D ?A ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseCDAStrictParallelogramm; [immParallelogramm | immClockwise]

	| H : Clockwise ?A ?B ?D |- StrictParallelogramm ?A ?B ?C ?D => apply ClockwiseDABStrictParallelogramm; [immParallelogramm | immClockwise]
	| H : Clockwise ?B ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseDABStrictParallelogramm; [immParallelogramm | immClockwise]
	| H : Clockwise ?D ?A ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply ClockwiseDABStrictParallelogramm; [immParallelogramm | immClockwise]

	| H : Clockwise ?A ?B (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseABKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise ?B (PCenter ?A ?B ?C ?D ?Hp) ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseABKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?A ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseABKStrictParallelogramm A B C D Hp); immClockwise

	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?B ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseBCKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise ?B ?C (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseBCKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise ?C (PCenter ?A ?B ?C ?D ?Hp) ?B |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseBCKStrictParallelogramm A B C D Hp); immClockwise

	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?C ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseCDKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise ?C ?D (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseCDKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise ?D (PCenter ?A ?B ?C ?D ?Hp) ?C |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseCDKStrictParallelogramm A B C D Hp); immClockwise

	| H : Clockwise ?A (PCenter ?A ?B ?C ?D ?Hp) ?D |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseDAKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise (PCenter ?A ?B ?C ?D ?Hp) ?D ?A |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseDAKStrictParallelogramm A B C D Hp); immClockwise
	| H : Clockwise ?D ?A (PCenter ?A ?B ?C ?D ?Hp) |- StrictParallelogramm ?A ?B ?C ?D  => apply (ClockwiseDAKStrictParallelogramm A B C D Hp); immClockwise

	|  |- StrictParallelogramm ?A ?B ?C (StrictPVertex4 ?A ?B ?C ?H) => apply (StrictPVertex4Parallelogramm A B C H)
	|  |- StrictParallelogramm ?B ?C (StrictPVertex4 ?A ?B ?C ?H) ?A =>apply StrictParallelogrammPerm; apply (StrictPVertex4Parallelogramm A B C H)
	|  |- StrictParallelogramm ?C (StrictPVertex4 ?A ?B ?C ?H) ?A ?B => do 2 apply StrictParallelogrammPerm; apply (StrictPVertex4Parallelogramm A B C H)
	|  |- StrictParallelogramm (StrictPVertex4 ?A ?B ?C ?H) ?A ?B ?C => do 3 apply StrictParallelogrammPerm; apply (StrictPVertex4Parallelogramm A B C H)
end.

Ltac immEqLine := match goal with 
	| |- EqLine ?d ?d  => apply EqLineRefl
	| H : EqLine ?d1 ?d2 |- EqLine ?d2 ?d1 => apply (EqLineSym d1 d2 H)
	| H : forall M : Point, OnLine ?d2 M -> OnLine ?d1 M |- EqLine ?d1 ?d2 => apply (OnLineEqLine d1 d2 H)
	| H : forall M : Point, OnLine ?d1 M -> OnLine ?d2 M |- EqLine ?d1 ?d2 => apply EqLineSym; apply (OnLineEqLine d2 d1 H)
	| |- EqLine (Ruler ?A ?B ?H1) (Ruler ?A ?B ?H2) => apply (EqLineId A B H1 H2)
	| |- EqLine (Ruler ?A ?B ?H1) (Ruler ?B ?A ?H2) => apply (EqLineOpp A B H1 H2)

	| |- EqLine ?d _ => unfold d; immEqLine
	| |- EqLine _ ?d => unfold d; immEqLine
end.

Ltac immParallelLines := match goal with 
	| |- ParallelLines ?d ?d  => apply ParallelLinesRefl
	| H : ParallelLines ?d1 ?d2 |- ParallelLines ?d2 ?d1 => apply (ParallelLinesSym d1 d2 H)
	| H : EqLine ?d1 ?d2 |- ParallelLines ?d1 ?d2 => apply (EqParallelLine d1 d2 H)
	| H : EqLine ?d1 ?d2 |- ParallelLines ?d2 ?d1 => apply ParallelLinesSym; apply (EqParallelLine d1 d2 H)

	| |- ParallelLines ?l (Parallel ?l ?A ?H) => apply (ParallelParallelLine l A H)
	| |- ParallelLines (Parallel ?l ?A ?H) ?l  => apply ParallelLinesSym; apply (ParallelParallelLine l A H)

	| |- EqLine ?d _ => unfold d; immParallelLines
	| |- EqLine _ ?d => unfold d; immParallelLines

	| _ => simplLine; immEquiDirected
end.

Ltac immSecantLines := match goal with 
	| H : SecantLines ?d1 ?d2 |- SecantLines ?d2 ?d1 => apply (SecantLinesSym d1 d2 H)
	| H : Perpendicular ?d1 ?d2 |- SecantLines ?d1 ?d2 => apply (PerpendicularSecant d1 d2 H)

	| |- EqLine ?d _ => unfold d; immSecantLines
	| |- EqLine _ ?d => unfold d; immSecantLines

	| _ => simplLine; immNotEquiDirected
end.

Ltac immNotEqLine := match goal with 
	| |- ~EqLine ?d1 ?d2 => apply (SecantNotEqLines d1 d2); immSecantLines
end.

Ltac immNotSecantLines := match goal with 
	| H : EqLine ?d1 ?d2 |- ~SecantLines ?d1 ?d2 => apply (EqNotSecantLines d1 d2 H)
	| H : EqLine ?d2 ?d1 |- ~SecantLines ?d1 ?d2 => apply (EqNotSecantLines d1 d2 (EqLineSym d2 d1 H))

	| H : ~SecantLines ?d2 ?d1 |- ~SecantLines ?d1 ?d2 => contrapose H; apply (SecantLinesSym d1 d2 H)

	| |- ~SecantLines ?d (Parallel ?d _ _) => apply ParallelNotSecant
	| |- ~SecantLines (Parallel ?d ?A ?H) ?d => let Hyp := fresh in (intro Hyp; elim Hyp; apply ParallelLinesSym; apply (ParallelParallelLine d A H))

	| _ => let Hyp := fresh in (intro Hyp; elim Hyp; immParallelLines)
end.

Ltac immPerpendicular := match goal with 
	| H : Perpendicular ?d1 ?d2 |- Perpendicular ?d2 ?d1 => apply (PerpendicularSym d1 d2 H)

	| |- Perpendicular (Ruler ?A ?B ?Hab) (MidLine ?A ?B ?Hab) => apply (PerpendicularMidLine A B Hab)
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?A ?B ?Hab) => apply PerpendicularSym; apply (PerpendicularMidLine A B Hab)

	| |- Perpendicular (Ruler ?A ?B ?Hab') (MidLine ?A ?B ?Hab) => apply (EqEqPerpendicular (Ruler A B Hab) (Ruler A B Hab') (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineId A B Hab Hab') |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?A ?B ?Hab') => apply PerpendicularSym; apply (EqEqPerpendicular (Ruler A B Hab) (Ruler A B Hab') (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineId A B Hab Hab') |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]

	| |- Perpendicular (Ruler ?B ?A ?Hba) (MidLine ?A ?B ?Hab) => apply (EqEqPerpendicular (Ruler A B Hab) (Ruler B A Hba) (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineOpp A B Hab Hba) |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]
	| |- Perpendicular (MidLine ?A ?B ?Hab) (Ruler ?B ?A ?Hba) => apply PerpendicularSym; apply (EqEqPerpendicular (Ruler A B Hab) (Ruler B A Hba) (MidLine A B Hab) (MidLine A B Hab)); [apply (EqLineOpp A B Hab Hba) |  apply EqLineRefl | apply (PerpendicularMidLine A B Hab)]

	| |- Perpendicular ?l (PerpendicularDown ?l ?A ?H) => apply (PerpendicularDownPerpendicular l A H)	| |- Perpendicular (PerpendicularDown ?l ?A ?H) ?l  => apply PerpendicularSym; apply (PerpendicularDownPerpendicular l A H)

	| |- Perpendicular ?l (PerpendicularUp ?l ?A ?H) => apply (PerpendicularUpPerpendicular l A H)	| |- Perpendicular (PerpendicularUp ?l ?A ?H) ?l  => apply PerpendicularSym; apply (PerpendicularUpPerpendicular l A H)

	| |- EqLine ?d _ => unfold d; immPerpendicular
	| |- EqLine _ ?d => unfold d; immPerpendicular
end.

(* par hypothses *)

Ltac immediate := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate
	| |- ?A \/ ?B => (left; immediate)  || (right; immediate)

	| |- DistancePlus _ _ = _ => solveDistance
	| |- _ = DistancePlus _ _ => solveDistance

	| |- DistanceTimes _ _ _ = _ => solveDistance
	| |- _ = DistanceTimes _ _ _ => solveDistance

	| |- Distance _ _ = _ => solveDistance
	| |- _ = Distance _ _ => solveDistance

	| |- IsDistance ?d => immIsDistance d

	| |- Supplementary _ _ = _ => solveSupplementary || (apply SupplementarySym; solveSupplementary)
	| |- _ = Supplementary _ _ => solveSupplementary || (apply SupplementarySym; solveSupplementary)

	| |-  Supplement _ _ _ _ _ _ => immSupplement
	| |-  OpposedAngles _ _ _ _ _ =>  apply OpposedAngleDef; immBetween

	| |- Angle _ _ _ _ _ = _ => solveAngle
	| |-  _ = Angle _ _ _ _ _ => solveAngle

	| |- CongruentAngle _ _ _ _ _ _ => immCongruentAngle
	| |- NullAngle _ _ _ => immNullAngle
	| |- ElongatedAngle _ _ _ => immElongatedAngle
	| |- RightAngle _ _ _ => immRightAngle
	| |- ~NullAngle _ _ _ => immNotNullAngle
	| |- ~ElongatedAngle _ _ _ => immNotElongatedAngle
	| |- ~RightAngle _ _ _ => immNotRightAngle

	| |- IsAngle _ => immIsAngle

	| |- _ = _ => solveEq
	| |- _ <> _ => immDistinct
	| |- ?A = ?B -> False => fold(A <> B); immDistinct

	| |- Clockwise _ _ _ => immClockwise
	| |- ~Clockwise _ _ _  => immNotClockwise
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise

	| |- Collinear _ _ _ => immCollinear
	| |- ~Collinear _ _ _  => immNotCollinear
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear

	| |- EquiOriented _ _ _ _ => immEquiOriented
	| |- OpenRay _ _ _ => immOpenRay
	| |- ClosedRay _ _ _ => immClosedRay
	| |- Between _ _ _ => immBetween
	| |- Segment _ _ _ => immSegment

	| |- EquiDirected _ _ _ _ => immEquiDirected
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected
	| |- EquiDirected ?A ?B ?C ?D  -> False => fold (~EquiDirected A B C D); immNotEquiDirected

	| |- DistanceLe _ _ => immDistanceLe
	| |- DistanceLt _ _ => immDistanceLt

	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec

	| |- Diameter _ _ => immDiameter
	| |- OnCircle _ _ => immOnCircle
	| |- OnLine _ _ => immOnLine

	| |- TStrict _ => immTStrict
	| |- Isosceles1 ?t => unfold t; immIsosceles1
	| |- Isosceles1 (Tr _ _ _) => immIsosceles1
	| |- Isosceles2 ?t => unfold t; immIsosceles2
	| |- Isosceles2 (Tr _ _ _) => immIsosceles2
	| |- Isosceles3 ?t => unfold t; immIsosceles3
	| |- Isosceles3 (Tr _ _ _) => immIsosceles3
	| |- Equilateral ?t => unfold t; immEquilateral
	| |- Equilateral (Tr _ _ _) => immEquilateral

	| |- TCongruent _ _ => immTCongruent

	| |- Parallelogramm _ _ _ _ => immParallelogramm
	| |- StrictParallelogramm _ _ _ _ => immStrictParallelogramm

	| |- EqLine _ _ => immEqLine
	| |- ~EqLine _ _ => immNotEqLine
	| |- EqLine ?d1 ?d2  -> False =>  fold (~EqLine d1 d2); immNotEqLine
	| |- ParallelLines _ _ => immParallelLines
	| |- SecantLines _ _ => immSecantLines
	| |- ~SecantLines _ _ => immNotSecantLines
	| |- SecantLines ?d1 ?d2  -> False =>  fold (~SecantLines d1 d2); immNotSecantLines
	| |- Perpendicular _ _ => immPerpendicular
end.
