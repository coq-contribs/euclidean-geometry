(* immediate *)

Ltac immClockwise1 := match goal with
	| H : Clockwise ?A ?B ?C |- Clockwise ?A ?B ?C => exact H	
	| H : Clockwise ?A ?B ?C |- Clockwise ?B ?C ?A => exact (ClockwiseBCA A B C H)
	| H : Clockwise ?A ?B ?C |- Clockwise ?C ?A ?B => exact (ClockwiseCAB A B C H)
end.

Ltac immDistinct1 := match goal with
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
end.

Ltac immCollinear1 := match goal with
	|  |- Collinear ?A ?A  _ => apply CollinearAAB	
	|  |- Collinear ?A _ ?A => apply CollinearABA	
	|  |- Collinear _ ?A ?A  => apply CollinearABB	

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

Ltac immNotClockwise1 := match goal with
	|  |- ~Clockwise ?A ?A _ => apply NotClockwiseAAB	
	|  |- ~Clockwise ?A _ ?A => apply NotClockwiseABA
	|  |- ~Clockwise _ ?A ?A => apply NotClockwiseABB

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

Ltac immNotCollinear1 := match goal with
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?A ?B ?C => exact H	
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?A ?C ?B => intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?B ?A ?C =>  intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?B ?C ?A =>  intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?C ?A ?B =>  intro; elim H; immCollinear1
	| H : ~Collinear ?A ?B ?C |- ~Collinear ?C ?B ?A =>  intro; elim H; immCollinear1
	|  |- ~Collinear ?A ?B ?C => apply ClockwiseABCNotCollinear; immClockwise1
	|  |- ~Collinear ?A ?B ?C => apply ClockwiseBACNotCollinear; immClockwise1
end.

Ltac immEquiOriented1 := match goal with
	| |- EquiOriented ?A ?A ?B ?C => apply EquiOrientedAABC
	| |- EquiOriented ?A ?B ?A ?B => canonize1
	| H : EquiOriented ?A ?B ?C ?D |- EquiOriented ?A ?B ?C ?D => trivial
	| H : forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D M |- EquiOriented ?A ?B ?C ?D => trivial

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
end.

Ltac immOpenRay1 := match goal with 
	| |- OpenRay ?A ?A ?B => apply OpenRayAAB
	| |- OpenRay ?A ?B ?B => apply OpenRayABB

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
end.

Ltac immClosedRay1 := apply OpenRayClosedRay; immOpenRay1.

Ltac immBetween1 :=  match goal with
	| H : Between ?A ?B ?C |- Between ?A ?B ?C => exact H
end.

Ltac immSegment1 := match goal with
	| |- Segment ?A ?B ?A => apply SegmentABA
	| |- Segment ?A ?B ?B => apply SegmentABB
	| H : Segment ?A ?B ?C |- Segment ?A ?B ?C => exact H
	| H : Segment ?A ?B ?C |- Segment ?B ?A ?C => apply (SegmentSym _ _ _ H)
	| H : Between ?A ?B ?C |- Segment ?A ?C ?B => apply (BetweenSegment A B C H)
	| H : Between ?A ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (BetweenSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?A ?C ?B => apply (EquiOrientedSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (EquiOrientedSegment A B C H)
end.

Ltac immEquiDirected1 := match goal with
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
end.

Ltac immNotEquiDirected1 := match goal with
	| H : ~EquiDirected ?A ?B ?C ?D |- ~EquiDirected ?A ?B ?C ?D => exact H
	| H : ~EquiDirected _ _ _ _  |- ~EquiDirected _ _ _ _  => contrapose0 H; immEquiDirected1
	| H : EquiDirected _ _ _ _  -> False |- ~EquiDirected _ _ _ _  => contrapose0 H; immEquiDirected1
	| H : ~Collinear _ _ _  |- ~EquiDirected _ _ _ _ => contrapose0 H; immCollinear1
	| H : Collinear _ _ _  -> False |- ~EquiDirected _ _ _ _ => contrapose0 H; immCollinear1
end.

Ltac immediate1 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- _ => assumption

	| |- ?A /\ ?B => split; immediate1
	| |- ?A \/ ?B => (left; immediate1)  || (right; immediate1)

	| |- _ <> _ => immDistinct1
	| |- ?A = ?B -> False => fold(A <> B); immDistinct1
	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise1
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise1
	| |- Collinear _ _ _ => immCollinear1
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1
	| |- EquiOriented _ _ _ _ => immEquiOriented1
	| |- OpenRay _ _ _ => immOpenRay1
	| |- ClosedRay _ _ _ => immClosedRay1
	| |- Between _ _ _ => immBetween1
	| |- Segment _ _ _ => immSegment1
	| |- EquiDirected _ _ _ _ => immEquiDirected1
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected1
	| |- EquiDirected ?A ?B ?C ?D  -> False =>fold (~EquiDirected A B C D); immNotEquiDirected1
end.

(*step *)

Ltac stepDistinct1 A B H := match type of H with

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

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac stepCollinear1 H := match type of H with

	| OnLine (Ruler _ _ _) _ =>  unfold OnLine in H; simpl in H; immCollinear1
	| Diameter (Ruler _ _ _) _ =>  unfold Diameter, OnLine in H; simpl in H; immCollinear1
	| OnLine ?l _ =>  unfold l, OnLine in H; simpl in H; immCollinear1
	| Diameter ?l _ =>  unfold l, Diameter, OnLine in H; simpl in H; immCollinear1

	| Collinear ?A ?B ?C => match goal with
		| Hab : A <> B |- Collinear A C ?D => apply (CollinearTrans A B C D Hab H); try immediate1
		| Hba : B <> A |- Collinear A C ?D => apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate1
		| Hab : A <> B |- Collinear C ?D A => apply CollinearBCA; apply (CollinearTrans A B C D Hab H); try immediate1
		| Hba : B <> A |- Collinear C ?D A => apply CollinearBCA; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate1
		| Hab : A <> B |- Collinear ?D A C => apply CollinearCAB ; apply (CollinearTrans A B C D Hab H); try immediate1
		| Hba : B <> A |- Collinear ?D A C => apply CollinearCAB ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate1
		| Hab : A <> B |- Collinear C A ?D => apply CollinearBAC ; apply (CollinearTrans A B C D Hab H); try immediate1
		| Hba : B <> A |- Collinear C A ?D => apply CollinearBAC ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate1
		| Hab : A <> B |- Collinear ?D C A => apply CollinearCBA; apply (CollinearTrans A B C D Hab H); try immediate1
		| Hba : B <> A |- Collinear ?D C A => apply CollinearCBA; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate1
		| Hab : A <> B |- Collinear A ?D C => apply CollinearACB ; apply (CollinearTrans A B C D Hab H); try immediate1
		| Hba : B <> A |- Collinear A ?D C => apply CollinearACB ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate1
		| Hab : B <> A |- Collinear B C ?D => apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate1
		| Hba : A <> B |- Collinear B C ?D => apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate1
		| Hab : B <> A |- Collinear C ?D B => apply CollinearBCA; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate1
		| Hba : A <> B |- Collinear C ?D B => apply CollinearBCA; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate1
		| Hab : B <> A |- Collinear ?D B C => apply CollinearCAB ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate1
		| Hba : A <> B |- Collinear ?D B C => apply CollinearCAB ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate1
		| Hab : B <> A |- Collinear C B ?D => apply CollinearBAC ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate1
		| Hba : A <> B |- Collinear C B ?D => apply CollinearBAC ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate1
		| Hab : B <> A |- Collinear ?D C B => apply CollinearCBA; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate1
		| Hba : A <> B |- Collinear ?D C B => apply CollinearCBA; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate1
		| Hab : B <> A |- Collinear B ?D C => apply CollinearACB ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate1
		| Hba : A <> B |- Collinear B ?D C => apply CollinearACB ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate1
		| Hab : C <> B |- Collinear C A ?D => apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate1
		| Hba : B <> C |- Collinear C A ?D => apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate1
		| Hab : C <> B |- Collinear A ?D C => apply CollinearBCA; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate1
		| Hba : B <> C |- Collinear A ?D C => apply CollinearBCA; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate1
		| Hab : C <> B |- Collinear ?D C A => apply CollinearCAB ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate1
		| Hba : B <> C |- Collinear ?D C A => apply CollinearCAB ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate1
		| Hab : C <> B |- Collinear A C ?D => apply CollinearBAC ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate1
		| Hba : B <> C |- Collinear A C ?D => apply CollinearBAC ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate1
		| Hab : C <> B |- Collinear ?D A C => apply CollinearCBA; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate1
		| Hba : B <> C |- Collinear ?D A C => apply CollinearCBA; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate1
		| Hab : C <> B |- Collinear C ?D A => apply CollinearACB ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate1
		| Hba : B <> C |- Collinear C ?D A => apply CollinearACB ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate1
		| Hab : B <> C |- Collinear B A ?D => apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate1
		| Hba : C <> B |- Collinear B A ?D => apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate1
		| Hab : B <> C |- Collinear A ?D B => apply CollinearBCA; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate1
		| Hba : C <> B |- Collinear A ?D B => apply CollinearBCA; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate1
		| Hab : B <> C |- Collinear ?D B A => apply CollinearCAB ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate1
		| Hba : C <> B |- Collinear ?D B A => apply CollinearCAB ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate1
		| Hab : B <> C |- Collinear A B ?D => apply CollinearBAC ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate1
		| Hba : C <> B |- Collinear A B ?D => apply CollinearBAC ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate1
		| Hab : B <> C |- Collinear ?D A B => apply CollinearCBA; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate1
		| Hba : C <> B |- Collinear ?D A B => apply CollinearCBA; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate1
		| Hab : B <> C |- Collinear B ?D A => apply CollinearACB ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate1
		| Hba : C <> B |- Collinear B ?D A => apply CollinearACB ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate1
		| Hab : A <> C |- Collinear A B ?D => apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate1
		| Hba : C <> A |- Collinear A B ?D => apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate1
		| Hab : A <> C |- Collinear B ?D A => apply CollinearBCA; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate1
		| Hba : C <> A |- Collinear B ?D A => apply CollinearBCA; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate1
		| Hab : A <> C |- Collinear ?D A B => apply CollinearCAB ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate1
		| Hba : C <> A |- Collinear ?D A B => apply CollinearCAB ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate1
		| Hab : A <> C |- Collinear B A ?D => apply CollinearBAC ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate1
		| Hba : C <> A |- Collinear B A ?D => apply CollinearBAC ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate1
		| Hab : A <> C |- Collinear ?D B A => apply CollinearCBA; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate1
		| Hba : C <> A |- Collinear ?D B A => apply CollinearCBA; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate1
		| Hab : A <> C |- Collinear A ?D B => apply CollinearACB ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate1
		| Hba : C <> A |- Collinear A ?D B => apply CollinearACB ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate1
		| Hab : C <> A |- Collinear C B ?D => apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate1
		| Hba : A <> C |- Collinear C B ?D => apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate1
		| Hab : C <> A |- Collinear B ?D C => apply CollinearBCA; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate1
		| Hba : A <> C |- Collinear B ?D C => apply CollinearBCA; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate1
		| Hab : C <> A |- Collinear ?D C B => apply CollinearCAB ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate1
		| Hba : A <> C |- Collinear ?D C B => apply CollinearCAB ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate1
		| Hab : C <> A |- Collinear B C ?D => apply CollinearBAC ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate1
		| Hba : A <> C |- Collinear B C ?D => apply CollinearBAC ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate1
		| Hab : C <> A |- Collinear ?D B C => apply CollinearCBA; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate1
		| Hba : A <> C |- Collinear ?D B C => apply CollinearCBA; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate1
		| Hab : C <> A |- Collinear C ?D B => apply CollinearACB ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate1
		| Hba : A <> C |- Collinear C ?D B => apply CollinearACB ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate1
		end

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac stepEquiOriented1 A B C D H := match type of H with

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

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac stepOpenRay1 A B C H := match type of H with

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

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac stepEquiOrientedClockwise1 H := match type of H with
	| EquiOriented ?A ?B ?C ?D => match goal with
			| |- Clockwise C D _ => apply H; try immClockwise1
			| |- Clockwise _ C D => apply ClockwiseCAB; apply H; try immClockwise1
			| |- Clockwise D _ C => apply ClockwiseBCA; apply H; try immClockwise1

			| |- Clockwise D C _ => let Hyp := fresh in (assert (Hyp : EquiOriented B A D C); [stepEquiOriented1 B A D C H | apply Hyp; try immClockwise1])
			| |- Clockwise _ D C => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented B A D C); [stepEquiOriented1 B A D C H | apply Hyp; try immClockwise1])
			| |- Clockwise C _ D => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented B A D C); [stepEquiOriented1 B A D C H | apply Hyp; try immClockwise1])

			| |- Clockwise A B _ => let Hyp := fresh in (assert (Hyp : EquiOriented C D A B); [stepEquiOriented1 C D A B H | apply Hyp; try immClockwise1])
			| |- Clockwise _ A B => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented C D A B); [stepEquiOriented1 C D A B H | apply Hyp; try immClockwise1])
			| |- Clockwise B _ A => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented C D A B); [stepEquiOriented1 C D A B H | apply Hyp; try immClockwise1])

			| |- Clockwise B A _ => let Hyp := fresh in (assert (Hyp : EquiOriented D C B A); [stepEquiOriented1 D C B A H | apply Hyp; try immClockwise1])
			| |- Clockwise _ B A => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented D C B A); [stepEquiOriented1 D C B A H | apply Hyp; try immClockwise1])
			| |- Clockwise A _ B => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented D C B A); [stepEquiOriented1 D C B A H | apply Hyp; try immClockwise1])
		end
end.

Ltac stepOpenRayClockwise1 H := match type of H with
	| EquiOriented ?A ?B ?A ?C => match goal with
			| |- Clockwise A C _ => apply H; try immClockwise1
			| |- Clockwise _ A C => apply ClockwiseCAB; apply H; try immClockwise1
			| |- Clockwise C _ A => apply ClockwiseBCA; apply H; try immClockwise1

			| |- Clockwise C A _ => let Hyp := fresh in (assert (Hyp : EquiOriented B A C A); [immEquiOriented1 | apply Hyp; try immClockwise1])
			| |- Clockwise _ C A => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented B A C A); [immEquiOriented1 | apply Hyp; try immClockwise1])
			| |- Clockwise A _ C => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented B A C A); [immEquiOriented1 | apply Hyp; try immClockwise1])

			| |- Clockwise A B _ => let Hyp := fresh in (assert (Hyp : EquiOriented A C A B); [immEquiOriented1 | apply Hyp; try immClockwise1])
			| |- Clockwise _ A B => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented A C A B); [immEquiOriented1 | apply Hyp; try immClockwise1])
			| |- Clockwise B _ A => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented A C A B); [immEquiOriented1 | apply Hyp; try immClockwise1])

			| |- Clockwise B A _ => let Hyp := fresh in (assert (Hyp : EquiOriented C A B A); [immEquiOriented1 | apply Hyp; try immClockwise1])
			| |- Clockwise _ B A => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented C A B A); [immEquiOriented1 | apply Hyp; try immClockwise1])
			| |- Clockwise A _ B => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented C A B A); [immEquiOriented1 | apply Hyp; try immClockwise1])
		end
end.

Ltac stepClockwise1 A B C H := match type of H with

	| OpenRay _ _ _ => unfold OpenRay in H; stepOpenRayClockwise1 H
	| ClosedRay _ _ _ => unfold ClosedRay in H; stepOpenRayClockwise1 H
	| forall M : Point, Clockwise ?D ?E M -> Clockwise ?D ?F M => fold (EquiOriented D E D F) in H; stepOpenRayClockwise1 H
	| forall M : Point, Clockwise ?D ?E M -> Clockwise ?F ?G M => fold (EquiOriented D E F G) in H; stepEquiOrientedClockwise1 H
	| EquiOriented _ _ _ _ => stepEquiOrientedClockwise1 H

	| Clockwise A ?D ?E => apply (OpenRaysClockwise A D E B C H); try immediate1
	| Clockwise ?E A ?D => apply (OpenRaysClockwise A D E B C (ClockwiseBCA _ _ _ H)); try immediate1
	| Clockwise ?D ?E A => apply (OpenRaysClockwise A D E B C (ClockwiseCAB _ _ _ H)); try immediate1
	| Clockwise B ?D ?E => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A H); try immediate1
	| Clockwise ?E B ?D => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A (ClockwiseBCA _ _ _ H)); try immediate1
	| Clockwise ?D ?E B => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A (ClockwiseCAB _ _ _ H)); try immediate1
	| Clockwise C ?D ?E => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B H); try immediate1
	| Clockwise ?E C ?D => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B (ClockwiseBCA _ _ _ H)); try immediate1
	| Clockwise ?D ?E C => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B (ClockwiseCAB _ _ _ H)); try immediate1

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac stepSegment1 A B C H := match type of H with

	| EquiOriented C B A ?D => apply (EquiOrientedClosedRaySegment A D C B H); try immediate1
	| ClosedRay A ?D C => apply (EquiOrientedClosedRaySegment A D C B); [try immediate1 | exact H]
	| _  => apply EquiOrientedSegment; stepEquiOriented1 A C C B H

	| ?C = ?D => (rewrite H || rewrite <- H); try immediate1
end.

Ltac step1 H := match goal with
	| |- ?A <> ?B => stepDistinct1 A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct1 A B H
	| |- Collinear _ _ _  => stepCollinear1 H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented1 A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay1 A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay1 A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise1 A B C H
	| |- Segment ?A ?B ?C  => stepSegment1 A B C H
end.

(* absurd *)

Ltac absurd1 H := match type of H with
	| False => elim H
	| Oo = Uu => elim DistinctOoUu; trivial
	| Uu = Oo => elim DistinctOoUu; auto
	| ?A <> ?A => elim H; trivial
	| LineA ?l = LineB ?l => elim (LineH l); auto
	| LineB ?l = LineA ?l => elim (LineH l); auto
	| Clockwise ?A ?A _  => elim (NotClockwiseAAB _ _ H)
	| Clockwise ?A _ ?A  => elim (NotClockwiseABA _ _ H)
	| Clockwise _ ?A ?A  => elim (NotClockwiseABB _ _ H)
	| ~Collinear ?A ?A _  => elim H; apply CollinearAAB
	| ~Collinear ?A _ ?A  => elim H; apply CollinearABA
	| ~Collinear _ ?A ?A  => elim H; apply CollinearABB
	| ~_ => elim H; immediate1
end.

Ltac exactClockwise1 H := first
[exact H
| exact (ClockwiseBCA _ _ _ H)
| exact (ClockwiseCAB _ _ _ H)].

Ltac exactCollinear1 H := first
[exact H
| exact (CollinearACB _ _ _ H)
| exact (CollinearBAC _ _ _ H)
| exact (CollinearBCA _ _ _ H)
| exact (CollinearCAB _ _ _ H)
| exact (CollinearCBA _ _ _ H)].

Ltac contradict1 H1 H2 := 
match type of H1 with

	| _ = _ => rewrite H1 in H2; absurd1 H2

	| ~_ =>
		match type of H2 with
			| _ = _ => rewrite H2 in H1; absurd1 H1
			| _ => elim H1; immediate1
		end

	| Clockwise _ _ _ => 
		match type of H2 with
			| _ = _ => rewrite H2 in H1; absurd1 H1
			| Clockwise _ _ _ => elim (ClockwiseNotClockwise _ _ _ H1); exactClockwise1 H2
			| Collinear _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear1
			| OpenRay _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear1
			| ClosedRay _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear1
			| Between _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear1
			| Segment _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear1
			| EquiOriented _ _ _ _ => contradict1 H2 H1
			| ~_ => elim H2; immediate1
		end

	| Collinear _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear1
			| EquiOriented _ _ _ _ => contradict1 H2 H1
			| ~_ => elim H2; immediate1
		end

	| OpenRay _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear1
			| EquiOriented _ _ _ _ => let Hyp := fresh in (assert (Hyp := OpenRayCollinear _ _ _ H1); contradict1 H2 Hyp)
			| ~_ => elim H2; immediate1
		end

	| ClosedRay _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear1
			| EquiOriented _ _ _ _ => let Hyp := fresh in (assert (Hyp := ClosedRayCollinear _ _ _ H1); contradict1 H2 Hyp)
			| ~_ => elim H2; immediate1
		end

	| Between _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear1
			| EquiOriented _ _ _ _ =>  let Hyp := fresh in (assert (Hyp := BetweenCollinear _ _ _ H1); contradict1 H2 Hyp)
			| ~_ => elim H2; immediate1
		end

	| Segment _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear1
			| EquiOriented _ _ _ _ =>  let Hyp := fresh in (assert (Hyp := SegmentCollinear _ _ _ H1); contradict1 H2 Hyp)
			| ~_ => elim H2; immediate1
		end

	| EquiOriented _ _ _ _ =>
		match type of H2 with
			| ~Collinear _ _ _ => elim H2; immCollinear1
			| Collinear _ _ _ => first
				[ elim (EquiOrientedABCDNotCollinearABC _ _ _ _ H1); [idtac | exactCollinear1 H2]
				| elim (EquiOrientedABCDNotCollinearBCD _ _ _ _ H1); [try immediate1 | try immediate1 | exactCollinear1 H2]]
			| Clockwise _ _ _ => first
				[elim (EquiOrientedNotClockwiseABC _ _ _ _ H1); exactClockwise1 H2
				 | elim (EquiOrientedNotClockwiseABD _ _ _ _ H1); exactClockwise1 H2
				| elim (EquiOrientedABCDNotClockwiseCDA  _ _ _ _ H1); [try immediate1 | idtac | exactClockwise1 H2]
				| elim (EquiOrientedABCDNotClockwiseDCA  _ _ _ _ H1); [try immediate1 | exactClockwise1 H2]
				| elim (EquiOrientedABCDNotClockwiseCDB  _ _ _ _ H1); [try immediate1 | try immediate1 | exactClockwise1 H2]
				| elim (EquiOrientedABCDNotClockwiseDCB  _ _ _ _ H1); [try immediate1 | exactClockwise1 H2]
				| elim (EquiOrientedABCDNotClockwiseBAD  _ _ _ _ H1); [try immediate1 | exactClockwise1 H2]
				| elim (EquiOrientedABCDNotClockwiseBAC  _ _ _ _ H1); [try immediate1 | try immediate1 | exactClockwise1 H2] ]
			| ~_ => elim H2; immediate1
		end

	| forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D  M => fold (EquiOriented A B C D) in H1; contradict1  H1 H2

	| _ => match type of H2 with
		| forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D  M => fold (EquiOriented A B C D) in H2; contradict1 H2 H1
		end
end. 

(* Cases *)

Ltac by4Cases1 A B C := decompose [or] (FourCases A B C).

Ltac by3Cases1 A B C := decompose [or] (ThreeCases A B C).

Ltac by2Cases1 H := match type of H with
	| Collinear ?A ?B ?C => decompose [or] (CollinearTwoCases A B C H)
	| ~Collinear ?A ?B ?C => decompose [or] (NotCollinearTwoCases A B C H)
	| ~Clockwise ?A ?B ?C => decompose [or] (NotClockwiseTwoCases A B C H)
end.

Ltac by2OnLineCases1 d M := destruct (OnOrNotOnLine d M).

Ltac by3SegmentCases1 H := match type of H with
	| Collinear ?A ?B ?C => decompose [or] (CollinearThreeCases A B C H)
end.

Ltac since1 txt := assert txt; try immediate1.

Ltac from1 H txt := assert txt; [(step1 H; try immediate1) | try immediate1].

Ltac as1 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate1 | (step1 Hyp; try immediate1)]).
