Ltac simplCircle2 := unfold uCircle in *; repeat match goal with
	| H: context [(Diameter _ _)] |- _ => unfold Diameter in H; simpl OnLine in H
	| |- context [(Diameter _ _)]  => 	unfold Diameter; simpl OnLine 
	| H: context [(SecantCircles _ _)] |- _ => unfold SecantCircles in H; decompose [and] H; clear H
	| |- context [(SecantCircles _ _)]  => unfold SecantCircles
end;
	simpl OnCircle in *; simpl Radius in *; simpl RadiusB in *; simpl RadiusA in *; simpl Center in *; repeat visibleConj0.

Ltac simplCircleHyp2 H :=
	unfold Diameter, SecantCircles, TriangleSpec in H; simpl RadiusB in H; simpl RadiusA in H; simpl Center in H.

Ltac immCollinear2 := match goal with
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

end.

Ltac immEquiOriented2 := match goal with
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

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?C ?B ?A ?B => apply (ChangeAllABCB _ _ _ H); try immDistinct1
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?B ?C ?A ?B => apply (ChangeAllABBC _ _ _ H); try immDistinct1
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?C ?A ?A ?B => apply (ChangeAllABCA _ _ _ H); try immDistinct1
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented  ?A ?C ?A ?B => apply (ChangeAllABAC _ _ _ H); try immDistinct1

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?B ?C ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct1
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?C ?B ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct1
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?A ?C ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct1
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented  ?C ?A ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct1

	| H : EquiOriented ?A ?B ?C ?B |- EquiOriented ?B ?A ?B ?C => apply (ChangeSenseABCB _ _ _ H)
	| H : EquiOriented ?A ?B ?B ?C |- EquiOriented ?B ?A ?C ?B => apply (ChangeSenseABBC _ _ _ H)
	| H : EquiOriented ?A ?B ?C ?A |- EquiOriented ?B ?A ?A ?C => apply (ChangeSenseABCA _ _ _ H)
	| H : EquiOriented ?A ?B ?A ?C |- EquiOriented ?B ?A ?C ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : OpenRay ?A ?B ?C |- EquiOriented ?A ?B ?A ?C => exact H
	| H : OpenRay ?A ?B ?C |- EquiOriented  ?A ?C ?A ?B => apply (ChangeAllABAC _ _ _ H); try immDistinct1
	| H : OpenRay ?A ?B ?C |- EquiOriented  ?C ?A ?B ?A => apply (ChangeSide _ _ _ _ H); try immDistinct1
	| H : OpenRay ?A ?B ?C |- EquiOriented ?B ?A ?C ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : ClosedRay ?A ?B ?C |- EquiOriented ?A ?C ?A ?B => exact H
	| H : ClosedRay ?A ?B ?C |- EquiOriented  ?A ?B ?A ?C => apply (ChangeAllABAC _ _ _ H); try immDistinct1
	| H : ClosedRay ?A ?B ?C |- EquiOriented  ?B ?A ?C ?A => apply (ChangeSide _ _ _ _ H); try immDistinct1
	| H : ClosedRay ?A ?B ?C |- EquiOriented ?C ?A ?B ?A => apply (ChangeSenseABAC _ _ _ H)

	| H : Between ?A ?B ?C |- EquiOriented ?A ?B ?B ?C => destruct H; trivial
	| H : Between ?A ?B ?C |- EquiOriented ?B ?C ?A ?B => let Hyp1 := fresh in (let Hyp2 := fresh in (destruct H as (Hyp1,Hyp2); apply (ChangeAllABBC _ _ _ Hyp2 Hyp1)))
	| H : Between ?A ?B ?C |- EquiOriented ?C ?B ?B ?A => let Hyp1 := fresh in (let Hyp2 := fresh in (destruct H as (Hyp1,Hyp2); apply (ChangeSide _ _ _ _ Hyp2 Hyp1)))
	| H : Between ?A ?B ?C |- EquiOriented  ?B ?A ?C ?B => let Hyp := fresh in (destruct H as (_,Hyp); apply (ChangeSenseABBC _ _ _ Hyp))

	| H : Archimed ?A ?B ?C |- EquiOriented ?A ?C ?A ?B => apply (ArchimedianClosedRay _ _ _ H)
	| H : Archimed ?A ?B ?C |- EquiOriented  ?A ?B ?A ?C => apply ChangeAllABAC; [apply (ArchimedianClosedRay _ _ _ H) |  try immDistinct1]
	| H : Archimed ?A ?B ?C |- EquiOriented  ?B ?A ?C ?A => apply ChangeSide; [apply (ArchimedianClosedRay _ _ _ H) |  try immDistinct1]
	| H : Archimed ?A ?B ?C |- EquiOriented ?C ?A ?B ?A => apply ChangeSenseABAC; apply (ArchimedianClosedRay _ _ _ H)
end.

Ltac immOpenRay2 := match goal with 
	| |- OpenRay ?A ?A ?B => apply OpenRayAAB
	| |- OpenRay ?A ?B ?B => apply OpenRayABB

	| |- OpenRay Oo (Distance _ _ ) Uu => apply ClosedRayOpenRay; apply IsDistanceDistance
	| |- OpenRay Oo (DistancePlus _ _ ) Uu => apply ClosedRayOpenRay; apply IsDistanceDistancePlus
	| |- OpenRay Oo (DistanceTimes _ _ _ ) Uu => apply ClosedRayOpenRay; apply IsDistanceDistanceTimes

	|  H : OpenRay ?A ?B ?C |- OpenRay ?A ?B ?C => trivial
	|  H : EquiOriented ?A ?B ?A ?C |- OpenRay ?A ?B ?C => unfold OpenRay; exact H
	| H : forall M : Point, Clockwise ?A ?B M -> Clockwise ?A ?C M |- OpenRay ?A ?B ?C ?D => trivial

	| H : ClosedRay ?A ?B ?C |- OpenRay ?A ?C ?B => apply ClosedRayOpenRay; exact H

	| H : Between ?A ?B ?C |- OpenRay ?A ?B ?C => apply BetweenOpenRayAB; exact H
	| H : Between ?A ?B ?C |- OpenRay ?A ?C ?B => apply BetweenOpenRayAC; exact H
	| H : Between ?A ?B ?C |- OpenRay ?C ?B ?A => apply BetweenOpenRayCB; exact H

	| H : Segment ?A ?B ?C |- OpenRay ?A ?C ?B => apply SegmentOpenRayAC; exact H
	| H : Segment ?A ?B ?C |- OpenRay ?B ?C ?A => apply SegmentOpenRayAC; apply (SegmentSym _ _ _ H)
	| H : Segment ?A ?B ?C |- OpenRay ?A ?B ?C => apply SegmentOpenRayAB; [exact H | immDistinct1]
	| H : Segment ?A ?B ?C |- OpenRay ?B ?A ?C => apply SegmentOpenRayAB; [apply (SegmentSym _ _ _ H) | immDistinct1]

	| H : OpenRay ?A ?B ?C |- OpenRay ?A ?C ?B => apply OpenRaySym; [immDistinct1 | exact H]
	| H : ClosedRay ?A ?B ?C |- OpenRay ?A ?B ?C =>  apply OpenRaySym; [immDistinct1 | apply ClosedRayOpenRay; exact H]

	| H : Archimed ?A ?B ?C |- OpenRay ?A ?C ?B => apply ClosedRayOpenRay; apply (ArchimedianClosedRay A B C H)
end.

Ltac immClosedRay2 := apply OpenRayClosedRay; immOpenRay2.

Ltac immIsDistance2 d  := match d with
	| Distance _ _ => apply IsDistanceDistance
	| DistancePlus _ _ => apply IsDistanceDistancePlus
	| DistanceTimes _ _ _ => apply IsDistanceDistanceTimes
	| _ => immediate1 || (unfold IsDistance; immClosedRay2)
end.

Ltac immSegment2 := match goal with
	| |- Segment ?A ?B ?A => apply SegmentABA
	| |- Segment ?A ?B ?B => apply SegmentABB
	| |- Segment Oo (DistancePlus?A ?B) ?A => apply IsDistanceSegmentDistancePlus; immIsDistance2 A
	| H : Segment ?A ?B ?C |- Segment ?A ?B ?C => exact H
	| H : Segment ?A ?B ?C |- Segment ?B ?A ?C => apply (SegmentSym _ _ _ H)
	| H : Between ?A ?B ?C |- Segment ?A ?C ?B => apply (BetweenSegment A B C H)
	| H : Between ?A ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (BetweenSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?A ?C ?B => apply (EquiOrientedSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (EquiOrientedSegment A B C H)
	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immDistanceLe2 := match goal with
	| |- DistanceLe Oo _ => apply DistanceLeOo
	| |- DistanceLe ?A ?A => apply DistanceLeRefl

	| |- DistanceLe (Distance ?A ?B) (Distance ?A ?C) => apply SegmentDistanceLe; immSegment2
	| |- DistanceLe (Distance ?B ?A) (Distance ?A ?C) => rewrite (DistanceSym B A); apply SegmentDistanceLe; immSegment2
	| |- DistanceLe (Distance ?A ?B) (Distance ?C ?A) =>  rewrite (DistanceSym C A); apply SegmentDistanceLe; immSegment2
	| |- DistanceLe (Distance ?B ?A) (Distance ?C ?A) => rewrite (DistanceSym B A);  rewrite (DistanceSym C A); apply SegmentDistanceLe; immSegment2

	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus ?A ?C) => apply LeftRegularDistanceLe; immDistanceLe2
	| |- DistanceLe (DistancePlus ?B ?A) (DistancePlus ?A ?C) => rewrite (DistancePlusCommut B A); apply LeftRegularDistanceLe; immDistanceLe2
	| |- DistanceLe (DistancePlus ?A ?B) (DistancePlus ?C ?A) =>  rewrite (DistancePlusCommut C A); apply LeftRegularDistanceLe; immDistanceLe2
	| |- DistanceLe (DistancePlus ?B ?A) (DistancePlus ?C ?A) => rewrite (DistancePlusCommut B A);  rewrite (DistancePlusCommut C A); apply LeftRegularDistanceLe; immDistanceLe2

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

	| |- DistanceLe ?A (DistancePlus ?A _) => apply DistanceLeDistancePlus; immIsDistance2 A
	| |- DistanceLe ?A (DistancePlus _ ?A) => rewrite DistancePlusCommut; apply DistanceLeDistancePlus; immIsDistance2 A

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

	| |- DistanceLe _ _ => unfold DistanceLe; immSegment2
end.

Ltac solveEq2 := match goal with
	| |- ?X = ?X => apply refl_equal
	| H : ?X = ?Y |- ?X = ?Y => exact H
	| H : ?Y = ?X |- ?X = ?Y => rewrite H; apply refl_equal

	| |- ?X = _ => unfold X; solveEq2
	| |- _ = ?Y => unfold Y; solveEq2
end.

Ltac simplDistance2 := intros; simplCircle2; repeat 
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
end).


Ltac generalizeDist A B := repeat
match goal with 
	| H : context[(Distance A B)] |- _ => generalize H; clear H
	| H : context[(Distance B A)] |- _ => generalize H; rewrite (DistanceSym B A); clear H
end.

Ltac setDistance A B d := generalizeDist A B;  pose (d := Distance A B); fold d; intros.

Ltac measureDistance A B d := 
	pose (d := Distance A B); 
	let Hyp := fresh in (assert (Hyp := IsDistanceDistance A B);
		 fold d in Hyp); fold d.

Ltac generalizeDistance2 := repeat
match goal with 
	| H : context[(Distance _ _)] |- _ => generalize H; clear H
	| H : context[(DistancePlus _ _)] |- _ => generalize H; clear H
	| H : context[(DistanceTimes _ _ _)] |- _ => generalize H; clear H
end.

Ltac unfactorizeDistance2 delta := repeat (match goal with
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

Ltac foldDistance2 := 
repeat (match goal with
| |- context [(Distance ?A ?B)] => try rewrite (DistanceSym B A); 
		let delta := fresh "delta" in (pose (delta := Distance A B); fold delta)
end).

Ltac substDistance2 :=  repeat 
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

Ltac unfoldDistance2 := 
 repeat rewrite <- DistancePlusAssoc;
repeat match goal with 
	| X : Point |- _ => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| Distance _ _ = _ =>clear H; unfactorizeDistance2 X; subst X
		| _ => fail
		end)
end.

Ltac headDistancePlus2 B X := match X with
	| (DistancePlus B ?Z) => idtac
	| (DistancePlus ?Z B) => rewrite (DistancePlusCommut Z B)
	| (DistancePlus ?Y ?Z) => headDistancePlus2 B Z; rewrite (DistancePlusAssoc Y B); rewrite (DistancePlusCommut Y B); rewrite <- (DistancePlusAssoc B Y)
end.


Ltac writeDistancePlus2 A B sigma := repeat
match goal with
	| |- context [(DistancePlus A B)] => fold sigma
	| |- context [(DistancePlus A (DistancePlus B ?X))] => rewrite (DistancePlusAssoc A B X); fold sigma
	| |- context [(DistancePlus A ?X)] => headDistancePlus2 B X; rewrite (DistancePlusAssoc A B); fold sigma
end.

Ltac foldDistancePlusRec2 A B := match B with
	| DistancePlus ?C ?D => foldDistancePlusRec2 C D
	| _ => let sigma := fresh "sigma" in (pose (sigma := DistancePlus A B); writeDistancePlus2 A B sigma)
end.

Ltac foldDistancePlus2 := 
repeat (match goal with
| |- context [(DistancePlus ?A ?B)] => foldDistancePlusRec2 A B
end).

Ltac unfoldDistancePlus2 :=  repeat match goal with 
	| X : Point |- _ => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| DistancePlus _ _ = _ =>clear H; subst X
		| DistanceTimes _ _ _ = _ =>clear H; subst X
		| Distance _ _ = _ =>clear H; subst X
		| _ => fail
		end)
end.

Ltac substDistancePlus2 :=  repeat 
(let Heq := fresh "Heq" in (
intro Heq;
match type of Heq with 
	| DistancePlus _ _ = _ => rewrite Heq
	| _ = DistancePlus _ _ => rewrite <- Heq
	| _ => fail
end) || intro);
 repeat rewrite <- DistancePlusAssoc.

Ltac solveOnCircleDist2 := match goal with
	| H : OnCircle (Compass _ _ _) ?A |- Distance ?A _ = _ => unfold OnCircle in H
	| H : OnCircle (Compass _ _ _) ?A |- Distance _ ?A = _ => unfold OnCircle in H
	| H : OnCircle (Compass _ _ _) ?A |- _ = Distance ?A _ => unfold OnCircle in H
	| H : OnCircle (Compass _ _ _) ?A |- _ = Distance _ ?A => unfold OnCircle in H
	| H : OnCircle ?c ?A |- Distance ?A _ = _ => unfold c, OnCircle in H
	| H : OnCircle ?c ?A |- Distance _ ?A = _ => unfold c, OnCircle in H
	| H : OnCircle ?c ?A |- _ = Distance ?A _ => unfold c, OnCircle in H
	| H : OnCircle ?c ?A |- _ = Distance _ ?A => unfold c, OnCircle in H
end.
 
Ltac foldDistanceTimes2 := 
repeat (match goal with
| |- context [(DistanceTimes ?n ?A ?B)] => try rewrite (DistanceTimesSym B A n); 
		let delta := fresh "delta" in (pose (delta := DistanceTimes n  A B); fold delta)
end).

Ltac unfoldDistanceTimes2 := 
repeat match goal with 
	| X : Point |- _ => let H := fresh in (assert (H := refl_equal X); unfold X in H; match type of H with
		| DistanceTimes _  _ _ = _ =>clear H; subst X
		| _ => fail
		end)
end.

Ltac substDistanceTimes2 :=  repeat 
(let Heq := fresh "Heq" in (
intro Heq;
match type of Heq with 
	| DistanceTimes _  _ _ = _ => rewrite Heq
	| _ = DistanceTimes _ _ _ => rewrite <- Heq
	| _ => fail
end) || intro).

Ltac solveDist2 := try solveOnCircleDist2; generalizeDistance2; foldDistance2; substDistance2; unfoldDistance2; solveEq2.

Ltac solveDistPlus2 := generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistancePlus2; unfoldDistancePlus2; substDistancePlus2; solveEq2.

Ltac solveDistTimes2 := generalizeDistance2; foldDistance2; substDistance2; generalizeDistance2;  unfoldDistance2; foldDistanceTimes2; unfoldDistanceTimes2; substDistanceTimes2; solveEq2.

Ltac solveDistance2 := try simplDistance2; match goal with
	| |- DistancePlus _ _ = _ => solveDistPlus2
	| |- _ = DistancePlus _ _ => solveDistPlus2

	| |- DistanceTimes _ _ _ = _ => solveDistTimes2
	| |- _ = DistanceTimes _ _ _ => solveDistTimes2

	| |- Distance _ _ = Oo => apply EqNullDistance; solveEq2
	| |- Oo = Distance _ _ => apply sym_eq; apply EqNullDistance; solveEq2

	| |- Distance _ _ = _ => solveDist2
	| |- _ = Distance _ _ => apply sym_eq; solveDist2

	| |- _ => solveEq2
end.

Ltac immTriangularInequality2 := match goal with
	| |- TriangularInequality ?A ?B ?B ?C ?A ?C => apply TriangularInequalityABBCAC
	| |- TriangularInequality ?A ?B ?B ?C ?C ?A => apply TriangularInequalityABBCCA
	| |- TriangularInequality ?A ?B ?C ?B ?A ?C => apply TriangularInequalityABCBAC
	| |- TriangularInequality ?A ?B ?C ?B ?C ?A => apply TriangularInequalityABCBCA
	| |- TriangularInequality ?B ?A ?B ?C ?A ?C => apply TriangularInequalityBABCAC
	| |- TriangularInequality ?B ?A ?B ?C ?C ?A => apply TriangularInequalityBABCCA
	| |- TriangularInequality ?B ?A ?C ?B ?A ?C => apply TriangularInequalityBACBAC
	| |- TriangularInequality ?B ?A ?C ?B ?C ?A => apply TriangularInequalityBACBCA
end.

Ltac immTriangleSpec2 := match goal with
	| |- TriangleSpec ?A ?B ?B ?C ?A ?C => apply TriangleSpecABBCAC
	| |- TriangleSpec ?A ?B ?B ?C ?C ?A => apply TriangleSpecABBCCA
	| |- TriangleSpec ?A ?B ?C ?B ?A ?C => apply TriangleSpecABCBAC
	| |- TriangleSpec ?A ?B ?C ?B ?C ?A => apply TriangleSpecABCBCA
	| |- TriangleSpec ?B ?A ?B ?C ?A ?C => apply TriangleSpecBABCAC
	| |- TriangleSpec ?B ?A ?B ?C ?C ?A => apply TriangleSpecBABCCA
	| |- TriangleSpec ?B ?A ?C ?B ?A ?C => apply TriangleSpecBACBAC
	| |- TriangleSpec ?B ?A ?C ?B ?C ?A => apply TriangleSpecBACBCA
end.

Ltac immOnCircle2 := match goal with
	| H : OnCircle ?c ?A |- OnCircle ?c ?A => exact H
	| |- OnCircle (Compass _ _ _) _ => simpl; solveDistance2
	| |- OnCircle ?c _ => unfold c; simpl; solveDistance2
end.

Ltac immDiameter2 := match goal with
	| |- Diameter lineOoUu uCircle => apply DiameterlineOoUuuCircle
	| |- _ => simplCircle2; immCollinear2
end.

Ltac immDistinct2 := match goal with
	| H : ?A <> ?B |- ?A <> ?B => exact H
	| H : ?A <> ?B |- ?B <> ?A => auto
	| H : ?A = ?B -> False |- ?A <> ?B => exact H
	| H : ?A = ?B -> False |- ?B <> ?A => auto

	| |- Oo <> Uu => exact DistinctOoUu
	| |- Uu <> Oo => apply sym_not_eq; exact DistinctOoUu

	| |- LineA ?l <> LineB ?l => apply (LineH l)
	| |- LineB ?l <> LineA ?l => apply (sym_not_eq (LineH l))

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

Ltac immediate2 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate2
	| |- ?A \/ ?B => (left; immediate2)  || (right; immediate2)

	| |- DistancePlus _ _ = _ => solveDistance2
	| |- _ = DistancePlus _ _ => solveDistance2

	| |- DistanceTimes _ _ _ = _ => solveDistance2
	| |- _ = DistanceTimes _ _ _ => solveDistance2

	| |- Distance _ _ = _ => solveDistance2
	| |- _ = Distance _ _ => solveDistance2

	| |- IsDistance ?d => immIsDistance2 d

	| |- _ = _ => solveEq2
	| |- _ <> _ => immDistinct2
	| |- ?A = ?B -> False => fold(A <> B); immDistinct1

	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise1
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise1
	| |- Collinear _ _ _ => immCollinear2
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1
	| |- EquiOriented _ _ _ _ => immEquiOriented2
	| |- OpenRay _ _ _ => immOpenRay2
	| |- ClosedRay _ _ _ => immClosedRay2
	| |- Between _ _ _ => immBetween1
	| |- Segment _ _ _ => immSegment2
	| |- EquiDirected _ _ _ _ => immEquiDirected1
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected1
	| |- EquiDirected ?A ?B ?C ?D  -> False =>fold (~EquiDirected A B C D); immNotEquiDirected1

	| |- DistanceLe _ _ => immDistanceLe2
	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality2
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec2
	| |- Diameter _ _ => immDiameter2
	| |- OnCircle _ _ => immOnCircle2
end.

Ltac stepEq2 X Y H  := match type of H with
	| X = ?Z => rewrite H; try solveEq2
	| Y = ?Z => rewrite H; try solveEq2
	| ?Z = X => rewrite <- H; try solveEq2
	| ?Z = Y => rewrite <- H; try solveEq2
	| ?Z = ?T => first 
			[let Hyp := fresh in (assert (Hyp : X=Z); [solveEq2 | rewrite Hyp; clear Hyp; rewrite H; try solveEq2]) |
			let Hyp := fresh in (assert (Hyp : Y=Z); [solveEq2 | rewrite Hyp ; clear Hyp; rewrite H; try solveEq2]) |
			let Hyp := fresh in (assert (Hyp : X=T); [solveEq2 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq2]) |
			let Hyp := fresh in (assert (Hyp : Y=T); [solveEq2 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq2])]
end.

Ltac writeDistancePlusIn2 A B sigma := repeat
match goal with
	| |- context [(DistancePlus A B)] => fold sigma
	| |- context [(DistancePlus B A)] =>  rewrite (DistancePlusCommut B A); fold sigma
	| |- context [(DistancePlus A (DistancePlus B ?X))] => rewrite (DistancePlusAssoc A B X); fold sigma
	| |- context [(DistancePlus B (DistancePlus A ?X))] => rewrite (DistancePlusAssoc B A X); rewrite (DistancePlusCommut B A); fold sigma
	| |- context [(DistancePlus A ?X)] => headDistancePlus2 B X; rewrite (DistancePlusAssoc A B); fold sigma
	| |- context [(DistancePlus B ?X)] => headDistancePlus2 A X; rewrite (DistancePlusAssoc B A);  rewrite (DistancePlusCommut B A); fold sigma
end.

Ltac foldDistancePlusRecIn2 H A B := match B with
	| DistancePlus ?C ?D => foldDistancePlusRecIn2 H C D
	| _ => let sigma := fresh "sigma" in (pose (sigma := DistancePlus A B); writeDistancePlusIn2 A B sigma; fold sigma in H)
end.

Ltac foldDistancePlusIn2 H := 
repeat (match type of H with
| context [(DistancePlus ?A ?B)] => foldDistancePlusRecIn2 H A B
end).

Ltac foldDistanceTimesIn2 H := 
simpl DistanceTimes; 
repeat (match type of H with
| context [(DistanceTimes ?n ?A ?B)] => try rewrite (DistanceTimesSym n B A);
		let delta := fresh "delta" in (pose (delta := DistanceTimes n A B); fold delta; fold delta in H)
| context[(Distance ?A ?B)] =>  try rewrite (DistanceSym B A); 
		let delta := fresh "delta" in (pose (delta := Distance A B); fold delta; fold delta in H)
end).

Ltac foldDistanceIn2 H := repeat 
match type of H with
| context[(Distance ?A ?B)] =>  try rewrite (DistanceSym B A); 
		let delta := fresh "delta" in (pose (delta := Distance A B); fold delta; fold delta in H)
end.

Ltac substDistanceIn2 H := rewrite H || rewrite <- H.

Ltac unfoldDistanceIn2 H := 
match type of H with
| ?X = ?Y =>  generalize H; clear H; try subst X; try subst Y; intro H
end. 

Ltac unfoldRec2 X :=
match X with
| DistancePlus ?L ?R => unfoldRec2 L || unfoldRec2 R
| _ => subst X
end.

Ltac unfoldDistancePlusIn2 H := repeat
match type of H with
| ?X = ?Y =>   generalize H; (unfoldRec2 X || unfoldRec2 Y); clear H; intro H
end. 

Ltac stepEqDistance2 H  := 
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

	| Point => apply trans_eq with (y := H)

end; try immediate2.

Ltac stepTriangleSpec2 A B C D E F H  := match type of H with
	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate2

	| TriangleSpec ?AA ?BB ?CC ?DD ?EE ?FF => apply (TriangleSpecEq AA BB CC DD EE FF A B C D E F H); try solveDistance2
end.

Ltac stepDistinct2 A B H := match type of H with

	| Clockwise ?C ?D A => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immClockwise1 | try immNotClockwise1]
	| Clockwise ?D A ?C => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immClockwise1 | try immNotClockwise1]
	| Clockwise A ?C ?D => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immClockwise1 | try immNotClockwise1]
	| Clockwise ?C ?D B => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immClockwise1 | try immNotClockwise1]
	| Clockwise ?D B ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immClockwise1 | try immNotClockwise1]
	| Clockwise B ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immClockwise1 | try immNotClockwise1]

	| Collinear ?C ?D A => apply (FigureDistinct (fun M => Collinear C D M) A B); [immCollinear1 | try immNotCollinear1]
	| Collinear ?D A ?C => apply (FigureDistinct (fun M => Collinear C D M) A B); [immCollinear1 | try immNotCollinear1]
	| Collinear A ?C ?D => apply (FigureDistinct (fun M => Collinear C D M) A B); [immCollinear1 | try immNotCollinear1]
	| Collinear ?C ?D B => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immCollinear1 | try immNotCollinear1]
	| Collinear ?D B ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immCollinear1 | try immNotCollinear1]
	| Collinear B ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immCollinear1 | try immNotCollinear1]

	| ~Clockwise ?C ?D B => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immClockwise1 | try immNotClockwise1]
	| ~Clockwise ?D B ?C => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immClockwise1 | try immNotClockwise1]
	| ~Clockwise B ?C ?D => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immClockwise1 | try immNotClockwise1]
	| ~Clockwise ?C ?D A => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immClockwise1 | try immNotClockwise1]
	| ~Clockwise ?D A ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immClockwise1 | try immNotClockwise1]
	| ~Clockwise A ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immClockwise1 | try immNotClockwise1]

	| ~Collinear ?C ?D B => apply (FigureDistinct (fun M => Collinear C D M) A B); [immCollinear1 | try immNotCollinear1]
	| ~Collinear ?D B ?C => apply (FigureDistinct (fun M => Collinear C D M) A B); [immCollinear1 | try immNotCollinear1]
	| ~Collinear B ?C ?D => apply (FigureDistinct (fun M => Collinear C D M) A B); [immCollinear1 | try immNotCollinear1]
	| ~Collinear ?C ?D A => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immCollinear1 | try immNotCollinear1]
	| ~Collinear ?D A ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immCollinear1 | try immNotCollinear1]
	| ~Collinear A ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immCollinear1 | try immNotCollinear1]

	| Distance ?C ?D = Distance A B =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 
	| Distance A B = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 
	| Distance ?C ?D = Distance B A =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 
	| Distance B A = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); try immediate2 

	| ?C = ?D => (rewrite H || rewrite <- H || apply (DistinctEqDistanceDistinct C D A B)); try immediate2 
end.

Ltac stepDistanceLe2 H := match type of H with
	| Distance ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLe (Distance A B) _ => rewrite H
		| |- DistanceLe (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLe _ (Distance A B) => rewrite H
		| |- DistanceLe _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLe (Distance C D) _ => rewrite <- H
		| |- DistanceLe (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLe _ (Distance C D) => rewrite <- H
		| |- DistanceLe _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| DistancePlus ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLe (DistancePlus A B) _ => rewrite H
		| |- DistanceLe (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLe _ (DistancePlus A B) => rewrite H
		| |- DistanceLe _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLe (Distance C D) _ => rewrite <- H
		| |- DistanceLe (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLe _ (Distance C D) => rewrite <- H
		| |- DistanceLe _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| Distance ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLe (Distance A B) _ => rewrite H
		| |- DistanceLe (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLe _ (Distance A B) => rewrite H
		| |- DistanceLe _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLe (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLe (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLe _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLe _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistancePlus ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLe (DistancePlus A B) _ => rewrite H
		| |- DistanceLe (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLe _ (DistancePlus A B) => rewrite H
		| |- DistanceLe _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLe (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLe (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLe _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLe _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistanceTimes ?n ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLe (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLe (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLe _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLe _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLe (Distance C D) _ => rewrite <- H
		| |- DistanceLe (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLe _ (Distance C D) => rewrite <- H
		| |- DistanceLe _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| Distance ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLe (Distance A B) _ => rewrite H
		| |- DistanceLe (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLe _ (Distance A B) => rewrite H
		| |- DistanceLe _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLe (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLe (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLe _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLe _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
	| DistanceTimes ?n ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLe (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLe (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLe _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLe _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLe (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLe (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLe _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLe _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistancePlus ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLe (DistancePlus A B) _ => rewrite H
		| |- DistanceLe (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLe _ (DistancePlus A B) => rewrite H
		| |- DistanceLe _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLe (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLe (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLe _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLe _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
	| DistanceTimes ?n ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLe (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLe (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLe _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLe _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLe (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLe (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLe _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLe _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end

	| DistanceLe ?A ?B => match goal with
		| |- DistanceLe A ?C => apply (DistanceLeTrans A B C H); try immediate2
		| |- DistanceLe ?C B => apply (DistanceLeTrans C A B C); [try immediate2 | exact H]
		end
end.

Ltac step2 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance2 H
	| |- _ = DistancePlus _ _  => stepEqDistance2 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance2 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance2 H
	| |- Distance _ _ = _ => stepEqDistance2 H
	| |- _ = Distance _ _ => stepEqDistance2 H

	| |- DistanceLe _ _  => stepDistanceLe2 H

	| |- ?A = ?B => stepEq2 A B H
	| |- ?A <> ?B => stepDistinct2 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct1 A B H

	| |- Collinear _ _ _  => stepCollinear1 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented1 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay1 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay1 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise1 A B C H
	| |- Segment ?A ?B ?C  => stepSegment1 A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec2 A B C D E F H
end.

Ltac setInterCircles c1 c2 J := match goal with
	| H : SecantCircles c1 c2 |- _ => let H1 := fresh "Hoc" in 
						let H2 := fresh "Hoc" in 
							let H3 := fresh "Hck" in  
								let H4 := fresh "Hun" in
						(destruct (InterCirclesPointDef   c1 c2 H) as (J, ((H1, (H2, H3)), H4));
							simpl in H1, H2, H3, H4)
	| _ => let H := fresh in (assert (H : SecantCircles c1 c2);
		[split; try immediate2 |  let H1 := fresh "Hoc" in 
					let H2 := fresh "Hoc" in 
						let H3 := fresh "Hck" in  
							let H4 := fresh "Hun" in
						(destruct (InterCirclesPointDef   c1 c2 H) as (J, ((H1, (H2, H3)), H4));
							simpl in H1, H2, H3, H4)])
end.
	
Ltac setInterDiameter l c J := match goal with
	| H : Diameter l c |- _ => let H1 := fresh "Hoc" in let H2 := fresh "Heo" in let H3 := fresh "Hun" in
					(destruct (InterDiameterPointDef  l c H) as (J, ((H1, H2), H3));
						 simpl in H1, H2, H3)
	|_ => let H := fresh in (assert (H : Diameter l c);
			[try immediate2 | let H1 := fresh "Hoc" in let H2 := fresh "Heo" in let H3 := fresh "Hun" in
					(destruct (InterDiameterPointDef  l c H) as (J, ((H1, H2), H3));
						 simpl in H1, H2, H3)])
end.

Ltac usingChasles2 A B C := match goal with
	| |- context [(DistancePlus (Distance A B) (Distance B C))] => rewrite (Chasles A B C); [try solveDistance2 | try immSegment2]
	| |- context [(DistancePlus (Distance B A) (Distance B C))] =>  rewrite (DistanceSym B A); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]
	| |- context [(DistancePlus (Distance A B) (Distance C B))] =>  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]
	| |- context [(DistancePlus (Distance B A) (Distance C B))] =>  rewrite (DistanceSym B A);  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]

	| |- context [(DistancePlus (Distance B C) (Distance A B))] => rewrite (DistancePlusCommut (Distance B C) (Distance A B)); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]
	| |- context [(DistancePlus (Distance B C) (Distance B A))] => rewrite (DistancePlusCommut (Distance B C) (Distance B A));  rewrite (DistanceSym B A); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]
	| |- context [(DistancePlus (Distance C B) (Distance A B))] => rewrite (DistancePlusCommut (Distance C B) (Distance A B));  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]
	| |- context [(DistancePlus (Distance C B) (Distance B A))] =>  rewrite (DistancePlusCommut (Distance C B) (Distance B A)); rewrite (DistanceSym B A);  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance2 | try immSegment2]

	| |- context [(Distance A C)] => rewrite <- (Chasles A B C);[idtac | try immSegment2]
	| |- context [(Distance C A)] => rewrite (DistanceSym C A); rewrite <- (Chasles A B C);[idtac | try immSegment2]

end.

Ltac usingChaslesRec2 := match goal with
	| |- Segment _ _ _ => apply ChaslesRec; try solveDistance2
end.

Ltac generalizeAll := repeat
match goal with 
   | H :  _  |- _ => generalize H; clear H
end.

Ltac since2 txt := assert txt; try immediate2.

Ltac from2 H txt := assert txt; [(step2 H;  try immediate2) | try immediate2].

Ltac as2 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate2 | (step2 Hyp;  try immediate2)]).
