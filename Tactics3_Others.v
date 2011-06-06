Load "Tactics2_Step.v".

(* Rappels : ces tactiques ont ete definies precedemment : 
par simplification en utilisant les definitions relatives a la droite, il vient 
simplLine
par simplification en utilisant les definitions relatives au cercle, il vient
simplCircle
simplCircleHyp
 par simplification en utilisant les definitions relatives a l'orientation, il vient
canonize 
 par simplification des relations de distance, il vient
simplDistance
Un parallelogramme strict est un parallelogramme.
 destructSP H
Par calcul sur les distances
solveDistance
 remplace les egalites d'angle par la relation
eqToCongruent
par contraposition avec l'hypothese "H"
contrapose H
simplification du but en utilisant les definitions
simplGoal
*)

(*  par simplification de l'hypothese "H" en utilisant les definitions relatives a l a droite , il vient : *)
Ltac simplLineHyp H  :=
	unfold SecantLines, ParallelLines in H; simpl OnLine in H; simpl LineH in H; simpl LineB in H; simpl LineA in H.


(* l'hypothese "H" est absurde *)
Ltac absurdHyp H := match type of H with
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
	| ~_ => elim H; immediate
end.

Ltac exactClockwise H := first
[exact H
| exact (ClockwiseBCA _ _ _ H)
| exact (ClockwiseCAB _ _ _ H)].

Ltac exactCollinear H := first
[exact H
| exact (CollinearACB _ _ _ H)
| exact (CollinearBAC _ _ _ H)
| exact (CollinearBCA _ _ _ H)
| exact (CollinearCAB _ _ _ H)
| exact (CollinearCBA _ _ _ H)].

(*  les hypotheses "H1" et "H2" sont contradictoires *)
Ltac contradict H1 H2 := 
match type of H1 with

	| _ = _ => rewrite H1 in H2; absurdHyp H2

	| ~_ =>
		match type of H2 with
			| _ = _ => rewrite H2 in H1; absurdHyp H1
			| _ => elim H1; immediate
		end

	| Clockwise _ _ _ => 
		match type of H2 with
			| _ = _ => rewrite H2 in H1; absurdHyp H1
			| Clockwise _ _ _ => elim (ClockwiseNotClockwise _ _ _ H1); exactClockwise H2
			| Collinear _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear
			| OpenRay _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear
			| ClosedRay _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear
			| Between _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear
			| Segment _ _ _ => elim (ClockwiseABCNotCollinear _ _ _ H1); immCollinear
			| EquiOriented _ _ _ _ => contradict H2 H1
			| ~_ => elim H2; immediate
		end

	| Collinear _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear
			| EquiOriented _ _ _ _ => contradict H2 H1
			| ~_ => elim H2; immediate
		end

	| OpenRay _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear
			| EquiOriented _ _ _ _ => let Hyp := fresh in (assert (Hyp := OpenRayCollinear _ _ _ H1); contradict H2 Hyp)
			| ~_ => elim H2; immediate
		end

	| ClosedRay _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear
			| EquiOriented _ _ _ _ => let Hyp := fresh in (assert (Hyp := ClosedRayCollinear _ _ _ H1); contradict H2 Hyp)
			| ~_ => elim H2; immediate
		end

	| Between _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear
			| EquiOriented _ _ _ _ =>  let Hyp := fresh in (assert (Hyp := BetweenCollinear _ _ _ H1); contradict H2 Hyp)
			| ~_ => elim H2; immediate
		end

	| Segment _ _ _ =>
		match type of H2 with
			| Clockwise _ _ _ =>  elim (ClockwiseABCNotCollinear _ _ _ H2); immCollinear
			| EquiOriented _ _ _ _ =>  let Hyp := fresh in (assert (Hyp := SegmentCollinear _ _ _ H1); contradict H2 Hyp)
			| ~_ => elim H2; immediate
		end

	| EquiOriented _ _ _ _ =>
		match type of H2 with
			| ~Collinear _ _ _ => elim H2; immCollinear
			| Collinear _ _ _ => first
				[ elim (EquiOrientedABCDNotCollinearABC _ _ _ _ H1); [idtac | exactCollinear H2]
				| elim (EquiOrientedABCDNotCollinearBCD _ _ _ _ H1); [try immediate1 | try immediate | exactCollinear H2]]
			| Clockwise _ _ _ => first
				[elim (EquiOrientedNotClockwiseABC _ _ _ _ H1); exactClockwise1 H2
				 | elim (EquiOrientedNotClockwiseABD _ _ _ _ H1); exactClockwise1 H2
				| elim (EquiOrientedABCDNotClockwiseCDA  _ _ _ _ H1); [try immediate | idtac | exactClockwise H2]
				| elim (EquiOrientedABCDNotClockwiseDCA  _ _ _ _ H1); [try immediate | exactClockwise H2]
				| elim (EquiOrientedABCDNotClockwiseCDB  _ _ _ _ H1); [try immediate | try immediate | exactClockwise H2]
				| elim (EquiOrientedABCDNotClockwiseDCB  _ _ _ _ H1); [try immediate | exactClockwise H2]
				| elim (EquiOrientedABCDNotClockwiseBAD  _ _ _ _ H1); [try immediate | exactClockwise H2]
				| elim (EquiOrientedABCDNotClockwiseBAC  _ _ _ _ H1); [try immediate | try immediate | exactClockwise H2] ]
			| ~_ => elim H2; immediate
		end

	| forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D  M => fold (EquiOriented A B C D) in H1; contradict  H1 H2

	| _ => match type of H2 with
		| forall M : Point, Clockwise ?A ?B M -> Clockwise ?C ?D  M => fold (EquiOriented A B C D) in H2; contradict H2 H1
		end
end. 

(* on distingue les 4 cas suivants : *)
(* - "A" "B" et "C" sont dextrogyres, *)
(* - "A" "C" et "B" sont dextrogyres, *)
(* - "C" est sur la demi-droite ["A""B"), *)
(* - "C" est sur la demi-droite ["B""A"). *)
Ltac by4Cases A B C := decompose [or] (FourCases A B C).

(* on distingue les 3 cas suivants : *)
(* - "A" "B" et "C" sont dextrogyres, *)
(* - "A" "C" et "B" sont dextrogyres, *)
(* - "A" "B" et "C" sont alignes. *)
Ltac by3Cases A B C := decompose [or] (ThreeCases A B C).

Ltac by2Cases H := match type of H with
(* "A" "B" et "C" etant alignes. on distingue les 2 cas suivants : *)
(* - "C" est sur la demi-droite ["A""B"), *)
(* - "C" est sur la demi-droite ["B""A"). *)
	| Collinear ?A ?B ?C => decompose [or] (CollinearTwoCases A B C H)
(*  "A" "B" et "C" n'etant pas alignes. on distingue les 2 cas suivants : *)
(* - "A" "B" et "C" sont dextrogyres, *)
(* - "A" "C" et "B" sont dextrogyres. *)
	| ~Collinear ?A ?B ?C => decompose [or] (NotCollinearTwoCases A B C H)
(*  "A" "B" et "C" n'etant pas dextrogyres. on distingue les 2 cas suivants : *)
(* - "A" "C" et "B" sont dextrogyres, *)
(* - "A" "B" et "C" sont alignes. *)
	| ~Clockwise ?A ?B ?C => decompose [or] (NotClockwiseTwoCases A B C H)
end.

(* un point appartient ou non a une droite *)
Ltac by2OnLineCases d M := destruct (OnOrNotOnLine d M).

(* si les points "A" "B" et "C" sont alignes, l'un est entre les deux autres, *)
Ltac by3SegmentCases H := match type of H with
	| Collinear ?A ?B ?C => decompose [or] (CollinearThreeCases A B C H)
end.

(* si les points "A" et "B" sont distincts, le point "C" est distinct de l'un d'eux, *)
Ltac  byApartCases A B C := match goal with
	| H : A <> B |- _ => destruct (Apart A B C H)
	| H : B <> A |- _ => destruct (Apart A B C  (sym_not_eq H)) 
	| H : A = B -> False |- _ => destruct (Apart A B C H)
	| H : B = A -> False |- _ => destruct (Apart A B C  (sym_not_eq H)) 
	| _ => let H := fresh in (assert (H : A <> B); [ try immDistinct1 | destruct (Apart A B C H)])
end.

(* en utilisant la relation de Chasles sur les points "A" "B" "C", *)
Ltac usingChasles A B C := match goal with

(* on remplace AB+BC par AC : *)
	| |- context [(DistancePlus (Distance A B) (Distance B C))] => rewrite (Chasles A B C); [try solveDistance | try immSegment]
	| |- context [(DistancePlus (Distance B A) (Distance B C))] =>  rewrite (DistanceSym B A); rewrite (Chasles A B C);[try solveDistance | try immSegment]
	| |- context [(DistancePlus (Distance A B) (Distance C B))] =>  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance | try immSegment]
	| |- context [(DistancePlus (Distance B A) (Distance C B))] =>  rewrite (DistanceSym B A);  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance | try immSegment]

	| |- context [(DistancePlus (Distance B C) (Distance A B))] => rewrite (DistancePlusCommut (Distance B C) (Distance A B)); rewrite (Chasles A B C);[try solveDistance | try immSegment]
	| |- context [(DistancePlus (Distance B C) (Distance B A))] => rewrite (DistancePlusCommut (Distance B C) (Distance B A));  rewrite (DistanceSym B A); rewrite (Chasles A B C);[try solveDistance | try immSegment]
	| |- context [(DistancePlus (Distance C B) (Distance A B))] => rewrite (DistancePlusCommut (Distance C B) (Distance A B));  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance | try immSegment]
	| |- context [(DistancePlus (Distance C B) (Distance B A))] =>  rewrite (DistancePlusCommut (Distance C B) (Distance B A)); rewrite (DistanceSym B A);  rewrite (DistanceSym C B); rewrite (Chasles A B C);[try solveDistance | try immSegment]

(* on remplace AC par AB+BC : *)
	| |- context [(Distance A C)] => rewrite <- (Chasles A B C);[idtac | try immSegment]
	| |- context [(Distance C A)] => rewrite (DistanceSym C A); rewrite <- (Chasles A B C);[idtac | try immSegment]

end.

(* en utilisant la reciproque de la relation de Chasles, il vient : *)
Ltac usingChaslesRec := match goal with
	| |- Segment _ _ _ => apply ChaslesRec; try solveDistance
end.

Ltac congruentToEqAngleHed A B C D E F Hba Hbc Hed := match goal with
	| Hef : E <> F |- _  =>  apply (CongruentEqAngle A B C D E F Hba Hbc Hed Hef)
	| Hef : E = F -> False |- _  =>  apply (CongruentEqAngle A B C D E F Hba Hbc Hed Hef)
	| _ =>  let Hef := fresh in (assert (Hef : E <> F); [try immediate |  apply (CongruentEqAngle A B C D E F Hba Hbc Hed Hef)])
end.

Ltac congruentToEqAngleHbc A B C D E F Hba Hbc:= match goal with
	| Hed : E <> D |- _  =>  congruentToEqAngleHed A B C D E F Hba Hbc Hed
	| Hed : E = D -> False |- _  =>  congruentToEqAngleHed A B C D E F Hba Hbc Hed
	| _ =>  let Hed := fresh in (assert (Hed : E <> D); [try immediate |  congruentToEqAngleHed A B C D E F Hba Hbc Hed])
end.

Ltac congruentToEqAngleHba A B C D E F Hba := match goal with
	| Hbc : B <> C |- _  =>  congruentToEqAngleHbc A B C D E F Hba Hbc
	| Hbc : B = C -> False |- _  =>  congruentToEqAngleHbc A B C D E F Hba Hbc
	| _ =>  let Hbc := fresh in (assert (Hbc : B <> C); [try immediate |  congruentToEqAngleHbc A B C D E F Hba Hbc])
end.

Ltac supplementAngleHed A B C D E F Hba Hbc Hed := match goal with
	| Hef : E <> F |- _  =>  apply (EqAngleSupplement A B C D E F Hba Hbc Hed Hef)
	| _ =>  let Hef := fresh in (assert (Hef : E <> F); [try immediate |  apply (EqAngleSupplement A B C D E F Hba Hbc Hed Hef)])
end.

Ltac supplementAngleHbc A B C D E F Hba Hbc:= match goal with
	| Hed : E <> D |- _  =>  supplementAngleHed A B C D E F Hba Hbc Hed
	| _ =>  let Hed := fresh in (assert (Hed : E <> D); [try immediate |  supplementAngleHed A B C D E F Hba Hbc Hed])
end.

Ltac supplementAngleHba A B C D E F Hba := match goal with
	| Hbc : B <> C |- _  =>  supplementAngleHbc A B C D E F Hba Hbc
	| _ =>  let Hbc := fresh in (assert (Hbc : B <> C); [try immediate |  supplementAngleHbc A B C D E F Hba Hbc])
end.

(* remplace les relations d'angles en egalite *)
Ltac congruentToEq := unfold NullAngle, ElongatedAngle, RightAngle in *;

(* dans les hypotheses *)
repeat match goal with

(* relation de congruencce *)
	| H : CongruentAngle ?A ?B ?C ?D ?E ?F |- _ => match goal with
		| Hba : B <> A, Hbc : B <> C, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (EqCongruentAngle A B C D E F Hba Hbc Hed Hef H)); clear H
		| _ => inversion_clear H
		end

(* angles supplementaires *)
	| H : Supplement ?A ?B ?C ?D ?E ?F |- _ => match goal with
		| Hba : B <> A, Hbc : B <> C, Hed : E <> D, Hef : E <> F |- _ => let Hyp := fresh in assert (Hyp := (SupplementSupplementary A B C D E F Hba Hbc Hed Hef H)); clear H
		| _ => inversion_clear H
		end

(* angles opposes *)
	| H : OpposedAngles ?A ?B ?C ?D ?E  |- _ => let Hyp := fresh in assert (Hyp := (OpposedCongruentAngles A B C D E H)); clear H
end; 

(* dans le but *)
match goal with
	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => 
		match goal with
			| Hba : B <> A |- _  => congruentToEqAngleHba A B C D E F Hba
			| _ =>  let Hba := fresh in (assert (Hba : B <> A); [try immediate | congruentToEqAngleHba A B C D E F Hba])
		end

	| |- Supplement ?A ?B ?C ?D ?E ?F => 
		match goal with
			| Hba : B <> A |- _  => supplementAngleHba A B C D E F Hba
			| _ =>  let Hba := fresh in (assert (Hba : B <> A); [try immediate | supplementAngleHba A B C D E F Hba])
		end 

	| _ => idtac
end.

(* premier cas d'egalite des triangles *)
Ltac SSS := usingSSS; try immediate.

(* deuxieme cas d'egalite des triangles *)
Ltac ASS := usingSASa; try immediate.
Ltac SAS := usingSASb; try immediate.
Ltac  SSA :=  usingSASc; try immediate.

(* troisieme cas d'egalite des triangles *)
Ltac AAS := usingASAab; try immediate.
Ltac SAA := usingASAbc; try immediate.
Ltac ASA := usingASAca; try immediate.

(* En utilisant le lemme de Pasch sur le triangle ABC, la droite l passant par le point D du cote AB passe par un point E situe soit sur un autre cote : *)
Ltac byPaschCases A B C D l E := match goal with
| Hn : ~Collinear A B C |- _ => match goal with
	| Hb : Between A D B |- _ => match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end])
		end
	| _ =>let Hb := fresh in (assert (Hb : Between A D B);
		[try immediate |  match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end])
		end])
	end
|  _ => let Hn := fresh in (assert (Hn : ~Collinear A B C);
	[try immediate | match goal with
	| Hb : Between A D B |- _ => match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end])
		end
	| _ =>let Hb := fresh in (assert (Hb : Between A D B);
		[try immediate |  match goal with
		|  Hd : OnLine l D |- _ => match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end
		|  _ =>let Hd := fresh in (assert (Hd : OnLine l D);
			[try immediate |  match goal with
			|  Hna : ~OnLine l A |- _ => match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end
			|  _ => let Hna := fresh in (assert (Hna : ~OnLine l A);
				[try immediate | match goal with
				| Hnb : ~OnLine l B |- _ => match goal with
					| Hnc : ~OnLine l C |- _ => 
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
					|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
						[try immediate |
						let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
					end
				|  _ => let Hnb := fresh in (assert (Hnb : ~OnLine l B);
					[try immediate | match goal with
						| Hnc : ~OnLine l C |- _ => 
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]
						|  _ => let Hnc := fresh in (assert (Hnc : ~OnLine l C) ;
							[try immediate |
							let Hypb := fresh in let Hypo := fresh in destruct (PaschLine A B C D l Hn Hb Hd Hna Hnb Hnc) as [(E, (Hypb, Hypo)) | (E, (Hypb, Hypo))]])
						end])
				end])
			end])
		end])
	end])
end.

(* On a "txt" : *)
Ltac since txt := assert txt; try immediate.

(* De "H" on deduit "txt" : *)
Ltac from H txt := assert txt; [(step H ; try immediate) |  try immediate].

(* Comme on a "txt", il vient : *)
Ltac asWeHave txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate |( step Hyp ; try immediate)]).

(* X repond a la question : *)
Ltac answerIs X := exists X; try immediate.
