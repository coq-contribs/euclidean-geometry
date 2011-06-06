Load "Tactics3_Others.v".

(* Soit "lineAB" la droite passant par "A" et "B". *)

Ltac setLine A B lineAB := match goal with
	| H : A <> B |- _ => pose (lineAB := Ruler A B H)
	| H : B <> A |- _ => pose (lineAB := Ruler A B (sym_not_eq H))
	| H : A = B -> False |- _ => pose (lineAB := Ruler A B H)
	| H : B = A -> False |- _ => pose (lineAB := Ruler A B (sym_not_eq H))
	| _ => let Hyp := fresh in (assert (Hyp : A<> B) ; [try immediate | pose (lineAB := Ruler A B Hyp)])
end.

(* Soit "gamma" le cercle de centre "C" et de rayon "AB". *)

Ltac setCircle C A B gamma := pose (gamma := Compass C A B).

(* Soit "M" le point d'intersection des cercles secantes "c1" et "c2", les trois points : centre de "c1", "M", centre de "c2" etant dextrogyres ou alignes. *)

Ltac setIntersectionCircles c1 c2 M := match goal with
	| H : SecantCircles c1 c2 |- _ => pose (M := IntersectionCirclesPoint c1 c2 H);
			let Hyp1 := fresh in (
				assert (Hyp1 := OnCircle1IntersectionCirclesPoint c1 c2 H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircle2IntersectionCirclesPoint c1 c2 H);
					let Hyp3 := fresh in (
						assert (Hyp3 := NotClockwiseIntersectionCirclesPoint c1 c2 H);
						fold M in Hyp1, Hyp2, Hyp3; simpl in Hyp1, Hyp2, Hyp3)))
	| H : SecantCircles c2 c1 |- _ => pose (M := IntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
			let Hyp1 := fresh in (
				assert (Hyp1 := OnCircle1IntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircle2IntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
					let Hyp3 := fresh in (
						assert (Hyp3 := NotClockwiseIntersectionCirclesPoint c1 c2 (SecantCirclesSym c2 c1 H));
						fold M in Hyp1, Hyp2, Hyp3; simpl in Hyp1, Hyp2, Hyp3)))
	| _ => let H := fresh in (
		assert (H : SecantCircles c1 c2);
		[(split; try immediate) |
			pose (M := IntersectionCirclesPoint c1 c2 H);
			let Hyp1 := fresh in (
				assert (Hyp1 := OnCircle1IntersectionCirclesPoint c1 c2 H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnCircle2IntersectionCirclesPoint c1 c2 H);
					let Hyp3 := fresh in (
						assert (Hyp3 := NotClockwiseIntersectionCirclesPoint c1 c2 H);
						fold M in Hyp1, Hyp2, Hyp3; simpl in Hyp1, Hyp2, Hyp3)))])
end.

(* Soit "C" un point tel que "A","B","C" soit dextrogyre. *)

Ltac setClockwise A B C := match goal with
	| H : A <> B |- _ => pose (C := ExistsClockwise A B H) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B H);
					fold C in Hyp)
	| H : B <> A |- _ => pose (C := ExistsClockwise A B (sym_not_eq H)) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
					fold C in Hyp)
	| H : A = B -> False |- _ => pose (C := ExistsClockwise A B H) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B H);
					fold C in Hyp)
	| H : B = A -> False |- _ => pose (C := ExistsClockwise A B  (sym_not_eq H)) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
					fold C in Hyp)
	| _ => let H := fresh in (
			assert (H : A <> B);
			[ try immediate | pose (C := ExistsClockwise A B H) ; 
				let Hyp := fresh in (
					assert (Hyp := ClockwiseExistsClockwise A B H);
					fold C in Hyp) ] )
end.

(* Soit "M" le point d'intersection des droites secantes "l1" et "l2". *)

Ltac setInterLines l1 l2 M := match goal with
	| H : SecantLines l1 l2 |- _ => pose (M := InterLinesPoint l1 l2 H);
			let Hyp1 := fresh in (
				assert (Hyp1 := OnLine1InterLinesPoint l1 l2 H);
				let Hyp2 := fresh in (
					assert (Hyp2 := OnLine2InterLinesPoint l1 l2 H);
					fold M in Hyp1, Hyp2))
	| H : SecantLines l2 l1 |- _ => pose (M := InterLinesPoint l1 l2 (SecantLinesSym l2 l1 H));
			let Hyp1 := fresh in (
				assert (Hyp1 := OnLine1InterLinesPoint l1 l2 (SecantLinesSym l2 l1 H));
				let Hyp2 := fresh in (
					assert (Hyp2 := OnLine2InterLinesPoint l1 l2 (SecantLinesSym l2 l1 H));
					fold M in Hyp1, Hyp2))
	| _ => let H := fresh in (
			assert (H : SecantLines l1 l2);
			[try immediate |
				pose (M := InterLinesPoint l1 l2 H);
				let Hyp1 := fresh in (
					assert (Hyp1 := OnLine1InterLinesPoint l1 l2 H);
					let Hyp2 := fresh in (
						assert (Hyp2 := OnLine2InterLinesPoint l1 l2 H);
						fold M in Hyp1, Hyp2))])
end.

(* Soit "E" le point intersection de la droite "(AB)" et de la droite "(CD)", les paires de points ("A","B") et ("C","D") n'ayant pas la meme direction. *)

Ltac setNotEquiDirectedInter A B C D E := match goal with
| H : ~EquiDirected A B C D |- _ => 
	pose (E := NotEquiDirectedInterPoint A B C D H);
	let Hyp1 := fresh in (
		assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D H);
		let Hyp2 :=fresh in (
			assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D H);
			fold E in Hyp1, Hyp2))

|  H1 : Clockwise A B C, H2 : ~Clockwise A B D |- _ => 
	pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
	let Hyp1 := fresh in (
		assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
		let Hyp2 :=fresh in (
			assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
			fold E in Hyp1, Hyp2))
|  H1 : Clockwise A B D, H2 : ~Clockwise A B C |- _ => 
	pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
	let Hyp1 := fresh in (
		assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
		let Hyp2 :=fresh in (
			assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
			fold E in Hyp1, Hyp2))
|  H1 : Clockwise C D A, H2 : ~Clockwise C D B |- _ => 
	pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
	let Hyp1 := fresh in (
		assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
		let Hyp2 :=fresh in (
			assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
			fold E in Hyp1, Hyp2))
|  H1 : Clockwise C D B, H2 : ~Clockwise C D A |- _ => 
	pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
	let Hyp1 := fresh in (
		assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
		let Hyp2 :=fresh in (
			assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
			fold E in Hyp1, Hyp2))

|  H1 : Clockwise A B C |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise A B D);
	[try immediate | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
				fold E in Hyp1, Hyp2))])
|  H1 : Clockwise A B D |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise A B C);
	[try immediate | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
				fold E in Hyp1, Hyp2))])
|  H1 : Clockwise C D A |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise C D B);
	[try immediate | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
				fold E in Hyp1, Hyp2))])
|  H1 : Clockwise C D B |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise C D A);
	[try immediate | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
				fold E in Hyp1, Hyp2))])

|  H2 : ~Clockwise A B D |- _ => let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[try immediate | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
				fold E in Hyp1, Hyp2))])
|  H2 : ~Clockwise A B C |- _ =>  let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[try immediate | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
				fold E in Hyp1, Hyp2))])
|  H2 : ~Clockwise C D B |- _ =>  let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[try immediate | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
				fold E in Hyp1, Hyp2))])
|  H2 : ~Clockwise C D A |- _ =>  let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
				fold E in Hyp1, Hyp2))])

|  _ => first
	[ let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[immediate | let H2 := fresh in (
		assert (H2 : ~Clockwise A B D);
		[try immediate | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
					fold E in Hyp1, Hyp2))])])
	| let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[immediate | let H2 := fresh in (
		assert (H2 : ~Clockwise A B C);
		[try immediate | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
					fold E in Hyp1, Hyp2))])])
	| let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[immediate | let H2 := fresh in (
		assert (H2 : ~Clockwise C D B);
		[try immediate | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
					fold E in Hyp1, Hyp2))])])
	| let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[immediate | let H2 := fresh in (
		assert (H2 : ~Clockwise C D A);
		[try immediate | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
					fold E in Hyp1, Hyp2))])])

	| let H2 := fresh in (
	assert (H2 : ~Clockwise A B D);
	[immediate | let H1 := fresh in (
		assert (H1 : Clockwise A B C);
		[try immediate | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : ~Clockwise A B C);
	[immediate | let H1 := fresh in (
		assert (H1 : Clockwise A B D);
		[try immediate | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : ~Clockwise C D B);
	[immediate | let H1 := fresh in (
		assert (H1 : Clockwise C D A);
		[try immediate | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : ~Clockwise C D A);
	[immediate | let H1 := fresh in (
		assert (H1 : Clockwise C D B);
		[try immediate | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
					fold E in Hyp1, Hyp2))])])

	| let H := fresh in (
	assert (H :~EquiDirected A B C D);
	[idtac |  pose (E := NotEquiDirectedInterPoint A B C D H);
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D H);
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D H);
				fold E in Hyp1, Hyp2))])]
end.

(* Soit "E" le point intersection de la droite "(AB)" et de la droite  "(CD)", les triplets ("A","B","C") et ("A","B","D") n'ayant pas la meme orientation. *)

Ltac setFourPointsInter A B C D E := match goal with
|  H1 : Clockwise A B C, H2 : Clockwise B A D |- _ => 
	pose (E := FourPointsInterPoint A B C D H1 H2);
	let Hyp1 := fresh in (
		assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
		let Hyp2 :=fresh in (
			assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
			fold E in Hyp1, Hyp2))
|  H1 : Clockwise A B D, H2 : Clockwise B A C |- _ => 
	pose (E := FourPointsInterPoint A B D C H1 H2);
	let Hyp1 := fresh in (
		assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
		let Hyp2 :=fresh in (
			assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
			fold E in Hyp1, Hyp2))
|  H1 : Clockwise C D A, H2 : Clockwise D C B |- _ => 
	pose (E := FourPointsInterPoint C D A B H1 H2);
	let Hyp1 := fresh in (
		assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
		let Hyp2 :=fresh in (
			assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
			fold E in Hyp1, Hyp2))
|  H1 : Clockwise C D B, H2 : Clockwise D C A |- _ => 
	pose (E := FourPointsInterPoint C D B A H1 H2);
	let Hyp1 := fresh in (
		assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
		let Hyp2 :=fresh in (
			assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
			fold E in Hyp1, Hyp2))

|  H1 : Clockwise A B C |- _ => let H2 := fresh in (
	assert (H2 : Clockwise B A D);
	[try immediate |
		pose (E := FourPointsInterPoint A B C D H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise B A D |- _ => let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[try immediate |
		pose (E := FourPointsInterPoint A B C D H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
				fold E in Hyp1, Hyp2))])

|  H1 : Clockwise A B D |- _ => let H2 := fresh in (
	assert (H2 : Clockwise B A C);
	[try immediate |
		pose (E := FourPointsInterPoint A B D C H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise B A C |- _ => let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[try immediate |
		pose (E := FourPointsInterPoint A B D C H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
				fold E in Hyp1, Hyp2))])

|  H1 : Clockwise C D A |- _ => let H2 := fresh in (
	assert (H2 : Clockwise D C B);
	[try immediate |
		pose (E := FourPointsInterPoint C D A B H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise D C B |- _ => let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[try immediate |
		pose (E := FourPointsInterPoint C D A B H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
				fold E in Hyp1, Hyp2))])

|  H1 : Clockwise C D B |- _ => let H2 := fresh in (
	assert (H2 : Clockwise D C A);
	[try immediate |
		pose (E := FourPointsInterPoint C D B A H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise D C A |- _ => let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[try immediate |
		pose (E := FourPointsInterPoint C D B A H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
				fold E in Hyp1, Hyp2))])
|  |- _ => first
	[ let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[immediate |
		let H2 := fresh in (
		assert (H2 : Clockwise B A D);
		[try immediate |
			pose (E := FourPointsInterPoint A B C D H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise B A D);
	[immediate |
		let H1 := fresh in (
		assert (H1 : Clockwise A B C);
		[try immediate |
			pose (E := FourPointsInterPoint A B C D H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[immediate |
		let H2 := fresh in (
		assert (H2 : Clockwise B A C);
		[try immediate |
			pose (E := FourPointsInterPoint A B D C H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise B A C);
	[immediate |
		let H1 := fresh in (
		assert (H1 : Clockwise A B D);
		[try immediate |
			pose (E := FourPointsInterPoint A B D C H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[immediate |
		let H2 := fresh in (
		assert (H2 : Clockwise D C B);
		[try immediate |
			pose (E := FourPointsInterPoint C D A B H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise D C B);
	[immediate |
		let H1 := fresh in (
		assert (H1 : Clockwise C D A);
		[try immediate |
			pose (E := FourPointsInterPoint C D A B H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[immediate |
		let H2 := fresh in (
		assert (H2 : Clockwise D C A);
		[try immediate |
			pose (E := FourPointsInterPoint C D B A H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise D C A);
	[immediate |
		let H1 := fresh in (
		assert (H1 : Clockwise C D B);
		[try immediate |
			pose (E := FourPointsInterPoint C D B A H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
					fold E in Hyp1, Hyp2))])])]
end.

(* Soit "M" le point intersection de la droite "l" et du cercle "c" tel que "(centre de c)M" ait la meme orientation que  "AB". *)

Ltac setInterDiameter l c M := match goal with
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
			[(simplCircle; simpl in |- *; try immediate) |
				pose (M := InterDiameterPoint l c H);
				let Hyp1 := fresh in (
					assert (Hyp1 := EquiOrientedInterDiameterPoint l c H);
					let Hyp2 := fresh in (
						assert (Hyp2 := OnCircleInterDiameterPoint l c H);
						let Hyp3 := fresh in (
							assert (Hyp3 := OnLineInterDiameterPoint l c H);
							simpl in *; fold M in Hyp1, Hyp2, Hyp3)))])
end.

(* Soit "M" le point intersection de la droite "l" et du cercle "c" tel que "(centre de c)M" ait la meme orientation que  "BA". *)

Ltac setSecondInterDiameter l c M := match goal with
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
			[(simplCircle; simpl in |- *; try immediate) |
				pose (M := SecondInterDiameterPoint l c H);
				let Hyp1 := fresh in (
					assert (Hyp1 := EquiOrientedSecondInterDiameterPoint l c H);
					let Hyp2 := fresh in (
						assert (Hyp2 := OnCircleSecondInterDiameterPoint l c H);
						let Hyp3 := fresh in (
							assert (Hyp3 := OnLineSecondInterDiameterPoint l c H);
							simpl in *; fold M in Hyp1, Hyp2, Hyp3)))])
end.

(* Soit "M" le point de la droite "(AB)" a distance "DE" du point "C" de la droite "(AB)" tel que "CM" ait la meme orientation que  "AB". *)

Ltac setAddSegment A B C D E M := match goal with
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
	[try immediate | pose (M := AddSegmentPoint A B C D E H H0); 
		let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
			let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 				let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
					fold M in Hyp1, Hyp2, Hyp3)))])

| H : A = B -> False |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate | pose (M := AddSegmentPoint A B C D E H H0); 
		let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
			let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 				let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
					fold M in Hyp1, Hyp2, Hyp3)))])

| H : B <> A, H0 : Collinear A B C |- _ => pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0); 			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))

| H : B = A -> False, H0 : Collinear A B C |- _ => pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0); 			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))

| H : B <> A |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate | pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0);			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))])

| H : B = A -> False |- _ => let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate | pose (M := AddSegmentPoint A B C D E (sym_not_eq H) H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E (sym_not_eq H) H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E (sym_not_eq H) H0);			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))])

| H0 : Collinear A B C |- _ => let H := fresh in (assert (H : A<> B) ; 
	[try immediate | pose (M := AddSegmentPoint A B C D E H H0); 
	let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
		let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 			let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
				fold M in Hyp1, Hyp2, Hyp3)))])

|  _ => let H := fresh in (assert (H : A<> B) ; 
	[try immediate | let H0 := fresh in (assert (H0 : Collinear A B C);
	[try immediate | pose (M := AddSegmentPoint A B C D E H H0); 
		let Hyp1 := fresh in (assert (Hyp1 := EquiOrientedAddSegmentPoint A B C D E H H0); 
			let Hyp2 := fresh in (assert (Hyp2 := EqDistanceAddSegmentPoint A B C D E H H0); 				let Hyp3 := fresh in (assert (Hyp3 := CollinearAddSegmentPoint A B C D E H H0); 
					fold M in Hyp1, Hyp2, Hyp3)))])])

end.

(* Soit "M" le point de la droite "(AB)" a distance "CD" de "A" du meme cote que "B". *)

Ltac setMarkSegment A B C D M := match goal with
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
	[try immediate | pose (M := MarkSegmentPoint A B C D Hyp); 
		let Hyp1 := fresh in (
			assert (Hyp1 := EqDistanceMarkSegmentPoint A B C D Hyp); 
			let Hyp2 := fresh in (
				assert (Hyp2 := ClosedRayMarkSegmentPoint A B C D Hyp); 
				fold M in Hyp1, Hyp2))])
end.

(* Soit "M" le point de la droite "(AB)" a distance "CD" de "A" a l'oppose de "B". *)

Ltac setOppSegment A B C D M := match goal with
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
				[try immediate  | pose (M := OppSegmentPoint A B C D Hyp); 
					let Hyp1 := fresh in (
						assert (Hyp1 := EqDistanceOppSegmentPoint A B C D Hyp); 
						let Hyp2 := fresh in (
							assert (Hyp2 := SegmentOppSegmentPoint A B C D Hyp); 
							fold M in Hyp1, Hyp2))])
end.

(* Soit "M" le point symetrique du point "A" par rapport au point "B". *)

Ltac setSymmetric A B M := match goal with
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
				[try immediate  | pose (M := SymmetricPoint A B Hyp); 
					let Hyp1 := fresh in (
						assert (Hyp1 := EqDistanceSymmetricPoint A B Hyp); 
						let Hyp2 := fresh in (
							assert (Hyp2 := BetweenSymmetricPoint A B Hyp); 
							fold M in Hyp1, Hyp2))])
end.

(* Soit "M" le point d'abscisse "n" sur la droite graduee "(AB)". *)

Ltac setGraduation n A B M := match goal with
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
				[try immediate  | pose (M := Graduation n A B Hyp); 
					let Hyp1 := fresh in (
						assert (Hyp1 := GraduationClosedRay n  A B Hyp); 
						let Hyp2 := fresh in (
						assert (Hyp2 := DistanceGraduation n A B Hyp); 
							fold M in Hyp1, Hyp2))])
end.

(* Soit "alpha" l'angle "ABC". *)

Ltac setAngle A B C alpha := match goal with
| Hba : B <> A, Hbc : B <> C |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B = A -> False, Hbc : B <> C |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B <> A, Hbc : B = C -> False |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B = A -> False, Hbc : B = C -> False |- _ =>  pose (alpha := Angle A B C Hba Hbc)
| Hba : B <> A |- _ =>  let Hbc := fresh in (
				assert (Hbc : B <> C);
				[try immediate | pose (alpha := Angle A B C Hba Hbc)])
| Hba : B = A -> False |- _ =>  let Hbc := fresh in (
				assert (Hbc : B <> C);
				[try immediate | pose (alpha := Angle A B C Hba Hbc)])
| Hbc : B <> C |- _ =>  let Hba := fresh in (
				assert (Hba : B <> A);
				[try immediate | pose (alpha := Angle A B C Hba Hbc)])
| Hbc : B = C -> False |- _ =>  let Hba := fresh in (
				assert (Hba : B <> A);
				[try immediate | pose (alpha := Angle A B C Hba Hbc)])
|  _ =>  let Hba := fresh in (
			assert (Hba : B <> A);
			[try immediate | let Hbc := fresh in (
				assert (Hbc : B <> C);
				[try immediate | pose (alpha := Angle A B C Hba Hbc)])])
end.

(* Soit "C" le troisieme sommet du triangle equilateral dextrogyre "ABC". *)

Ltac setEquilateral A B C := match goal with
	| H : A <> B |- _ => pose (C := ExistsClockwise A B H); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B H);
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B H); 
				fold C in Hyp, t))
	| H : B <> A |- _ => pose (C := ExistsClockwise A B (sym_not_eq H)); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B (sym_not_eq H)); 
				fold C in Hyp, t))
	| H : A = B -> False |- _ => pose (C := ExistsClockwise A B H); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B H);
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B H); 
				fold C in Hyp, t))
	| H : B = A -> False |- _ => pose (C := ExistsClockwise A B (sym_not_eq H)); 
		let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B  (sym_not_eq H));
			let t := fresh "t"  in (
				assert (t := EquilateralExistsClockwise A B (sym_not_eq H)); 
				fold C in Hyp, t))
	| _ => let H := fresh in (
			assert (H : A<> B) ; 
			[try immediate | pose (C := ExistsClockwise A B H); 
				let Hyp := fresh in (assert (Hyp := ClockwiseExistsClockwise A B H);
					let t := fresh "t"  in (
						assert (t := EquilateralExistsClockwise A B H); 
						fold C in Hyp, t))])
end.

(* Soit "F" le troisieme sommet du triangle "DEF" egal au triangle "ABC". *)

Ltac setTCongruent A B C D E F := match goal with
	| Hab : A <> B, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))
	| Hab : A = B -> False, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))
	| Hba : B <> A, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))
	| Hba : B = A -> False, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))
	| Hab : A <> B  |- _ => let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate | pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))])
	| Hab : A = B -> False  |- _ => let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate | pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
				fold F in Hyp1, Hyp2))])
	| Hba : B <> A  |- _ =>  let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate | pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))])
	| Hba : B = A -> False  |- _ =>  let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate | pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E (sym_not_eq Hba) He); 
				fold F in Hyp1, Hyp2))])
	| _ => let Hab := fresh in 
			(assert (Hab : A<> B) ; 
			[try immediate |  let He := fresh in
				(assert (He :  Distance A B = Distance D E) ;
				[try immediate | pose (F := ThirdVertex A B C D E Hab He); 
					let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
						let Hyp2 := fresh  in (assert (Hyp2 := ThirdVertexNotClockwise A B C D E Hab He); 
							fold F in Hyp1, Hyp2))])])
end.

(* Soit "F" le troisieme sommet du triangle "DEF" dextrogyre egal au triangle non degenere "ABC". *)

Ltac setTCongruentClockwise A B C D E F := match goal with
	| Hn : ~Collinear A B C, Hab : A <> B, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
				fold F in Hyp1, Hyp2))
	| Hn : ~Collinear A B C, Hba : B <> A, He : Distance A B = Distance D E  |- _ => pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E  (sym_not_eq Hba) He Hn); 
				fold F in Hyp1, Hyp2))
	| Hn : ~Collinear A B C, Hab : A <> B  |- _ => let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate | pose (F := ThirdVertex A B C D E Hab He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
				fold F in Hyp1, Hyp2))])
	| Hn : ~Collinear A B C, Hba : B <> A  |- _ =>  let He := fresh in
		(assert (He :  Distance A B = Distance D E) ;
		[try immediate | pose (F := ThirdVertex A B C D E (sym_not_eq Hba) He); 
		let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E (sym_not_eq Hba) He);
			let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E  (sym_not_eq Hba) He Hn); 
				fold F in Hyp1, Hyp2))])
	| Hn : ~Collinear A B C  |- _ => let Hab := fresh in 
			(assert (Hab : A<> B) ; 
			[try immediate |  let He := fresh in
				(assert (He :  Distance A B = Distance D E) ;
				[try immediate | pose (F := ThirdVertex A B C D E Hab He); 
					let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
						let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
							fold F in Hyp1, Hyp2))])])
	| _ => let Hn := fresh in 
	(assert (Hn : ~Collinear A B C);
	[try immediate | let Hab := fresh in 
			(assert (Hab : A<> B) ; 
			[try immediate |  let He := fresh in
				(assert (He :  Distance A B = Distance D E) ;
				[try immediate | pose (F := ThirdVertex A B C D E Hab He); 
					let Hyp1 := fresh in (assert (Hyp1 := ThirdVertexTCongruent A B C D E Hab He);
						let Hyp2 := fresh  in (assert (Hyp2 := NotCollinearThirdVertexClockwise A B C D E Hab He Hn); 
							fold F in Hyp1, Hyp2))])])])
end.

(* Soit "t" le triangle "ABC". *)

Ltac setTriangle A B C t := pose (t:=Tr A B C).

(* Soit "beta" l'angle supplementaire de l'angle "alpha". *)

Ltac setSupplementary alpha beta := match goal with
| H : IsAngle alpha |- _ =>  pose (beta := Supplementary alpha H);
					let Hyp := fresh in 
						(assert (Hyp := IsAngleSupplementary alpha H); fold beta in Hyp)
|  _ =>  let H := fresh in (
			assert (H : IsAngle alpha);
			[try immediate | pose (beta := Supplementary alpha H);
				let Hyp := fresh in 
					(assert (Hyp := IsAngleSupplementary alpha H); fold beta in Hyp)])
end.

(* Soit "m" la mediatrice du segment "[AB]". *)

Ltac setMidLine A B m := match goal with
| H : A <> B |- _ => pose (m := MidLine A B H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B H);
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B H);
			let Hyp3 := fresh in (
				assert (Hyp3 := PerpendicularMidLine A B H);
				fold m in Hyp1, Hyp2, Hyp3)))
| H : A = B -> False |- _ => pose (m := MidLine A B H); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B H);
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B H);
			let Hyp3 := fresh in (
				assert (Hyp3 := PerpendicularMidLine A B H);
				fold m in Hyp1, Hyp2, Hyp3)))
| H : B <> A |- _ => pose (m := MidLine A B (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B (sym_not_eq H));
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B (sym_not_eq H));
			let Hyp3 := fresh in (
				assert (Hyp3 := PerpendicularMidLine A B (sym_not_eq H));
				fold m in Hyp1, Hyp2, Hyp3)))
| H : B = A -> False |- _ => pose (m := MidLine A B (sym_not_eq H)); 
	let Hyp1 := fresh in (
		assert (Hyp1 := OnMidLineEqDistance A B (sym_not_eq H));
		let Hyp2 := fresh in (
			assert (Hyp2 := EqDistanceOnMidLine A B (sym_not_eq H));
			let Hyp3 := fresh in (
				assert (Hyp3 := PerpendicularMidLine A B (sym_not_eq H));
				fold m in Hyp1, Hyp2, Hyp3)))
| _ => let H := fresh in (
	assert (H : A <> B);
	[try immediate | pose (m := MidLine A B H); 
		let Hyp1 := fresh in (
			assert (Hyp1 := OnMidLineEqDistance A B H);
			let Hyp2 := fresh in (
				assert (Hyp2 := EqDistanceOnMidLine A B H);
				let Hyp3 := fresh in (
					assert (Hyp3 := PerpendicularMidLine A B H);
					fold m in Hyp1, Hyp2, Hyp3)))])
end.

(* Soit "C" le milieu du segment "[AB]". *)

Ltac setMidPoint A B C :=
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
	[try immediate | pose (C := MidPoint A B H);
		let Hyp1 := fresh in (
			assert (Hyp1 := MidPointBetween A B H);
			let Hyp2 := fresh in (
				assert (Hyp2 := MidPointEqDistance A B H);
				fold C in Hyp1, Hyp2))])
end.

(* Soit "D" le quatrieme sommet du parallelogramme "ABCD". *)

Ltac setParallelogramm A B C D := match goal with
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
				[try immediate |
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
				[try immediate |
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
			[try immediate |
			pose (D := SymmetricPoint B (MidPoint A C (sym_not_eq Hca)) Hbk);
			let Hyp := fresh in (
				assert (Hyp := (ParallelogrammVertex4 A B C (sym_not_eq Hca) Hbk)); 
				fold D in Hyp;
				fold K in Hbk, D)]))
	| Hca : C = A -> False |- _ => let K := fresh in (
		pose (K := MidPoint A C (sym_not_eq Hca));
		let Hbk := fresh in (
			assert (Hbk : B <> MidPoint A C (sym_not_eq Hca));
			[try immediate |
			pose (D := SymmetricPoint B (MidPoint A C (sym_not_eq Hca)) Hbk);
			let Hyp := fresh in (
				assert (Hyp := (ParallelogrammVertex4 A B C (sym_not_eq Hca) Hbk)); 
				fold D in Hyp;
				fold K in Hbk, D)]))
	| _ => let Hac := fresh in (
		assert (Hac : A <> C);
		[ try immediate |
		 let K := fresh in (
		pose (K := MidPoint A C Hac);
		let Hbk := fresh in (
			assert (Hbk : B <> MidPoint A C Hac);
			[try immediate |
			pose (D := SymmetricPoint B (MidPoint A C Hac) Hbk);
			let Hyp := fresh in (
				assert (Hyp := (ParallelogrammVertex4 A B C Hac Hbk)); 
				fold D in Hyp;
				fold K in Hbk, D)]))])
end.

(* Soit "D" le quatrieme sommet du parallelogramme strict "ABCD". *)

Ltac setStrictParallelogramm A B C D := match goal with
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
		[ try immediate |
		 pose (D := StrictPVertex4 A B C H);
		let Hyp := fresh in  (
			pose (Hyp := (StrictPVertex4Parallelogramm A B C H)); 
			fold D in Hyp)])
end.

(* Soit "K" le centre du parallelogramme "ABCD". *)

Ltac setParallelogrammCenter A B C D K := match goal with
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
	[try immediate |
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

(* Soit "K" le centre du parallelogramme strict "ABCD". *)

Ltac setStrictParallelogrammCenter A B C D K := match goal with
| Hs : StrictParallelogramm A B C D |- _ => DestructSP11 Hs;
	match goal with
	| H : StrictParallelogramm A B C D |- _ => pose (K := SPCenter A B C D H);
		let Hyp1 := fresh in (
			assert (Hyp1 := StrictParallelogrammClockwiseABK A B C D H);
			let Hyp2 := fresh in (
				assert (Hyp2 := StrictParallelogrammClockwiseBCK A B C D H);
				let Hyp3 := fresh in (
					assert (Hyp3 := StrictParallelogrammClockwiseCDK A B C D H);
					let Hyp4 := fresh in (
						assert (Hyp4 := StrictParallelogrammClockwiseDAK A B C D H);
						fold K in Hyp1, Hyp2, Hyp3, Hyp4))))
	end; match goal with
	| Hp : Parallelogramm A B C D |- _ =>  let Hyp0 := fresh in (
		assert (Hyp0 : PCenter A B C D Hp = K);
			[auto | let Hyp1 := fresh in (
				assert (Hyp1 := PCenterBetweenAC A B C D Hp);
				let Hyp2 := fresh in (
					assert (Hyp2 := PCenterBetweenBD A B C D Hp);
					let Hyp3 := fresh in (
						assert (Hyp3 := PCenterEqDistanceAC A B C D Hp);
						let Hyp4 := fresh in (
							assert (Hyp4 := PCenterEqDistanceBD A B C D Hp);
							rewrite Hyp0 in Hyp1;
							rewrite Hyp0 in Hyp2;
							rewrite Hyp0 in Hyp3;
							rewrite Hyp0 in Hyp4))))])
	end
end.

(* Soit "M" le point d'intersection des deux droites perpendiculaires "d1" et "d2". *)

Ltac setPerpendicularPoint d1 d2 M := match goal with
| H : Perpendicular d1 d2 |- _ =>
	pose (M := PerpendicularPoint d1 d2 H);
	let Hyp1 := fresh in (
		assert (PerpendicularPointOnLine1 d1 d2 H);
		let Hyp2 := fresh in (
			assert (PerpendicularPointOnLine2 d1 d2 H);
			fold M in Hyp1, Hyp2))
| H : Perpendicular d2 d1 |- _ =>
	pose (M := PerpendicularPoint d1 d2 (PerpendicularSym d2 d1 H));
	let Hyp1 := fresh in (
		assert (PerpendicularPointOnLine1 d1 d2 (PerpendicularSym d2 d1 H));
		let Hyp2 := fresh in (
			assert (PerpendicularPointOnLine2 d1 d2 (PerpendicularSym d2 d1 H));
			fold M in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : Perpendicular d1 d2);
	[try immediate |
	pose (M := PerpendicularPoint d1 d2 H);
	let Hyp1 := fresh in (
		assert (PerpendicularPointOnLine1 d1 d2 H);
		let Hyp2 := fresh in (
			assert (PerpendicularPointOnLine2 d1 d2 H);
			fold M in Hyp1, Hyp2))])
end.

(* Soit "l2" la droite poerepndiculaire a "l1" abaissee du point "A". *)

Ltac setPerpendicularDown l1 A l2 := match goal with
| H : ~OnLine l1 A |- _ => 
	pose (l2 := PerpendicularDown l1 A H);
	let Hyp1 := fresh in (
		assert (Hyp1 := PerpendicularDownOnLine l1 A H);
		let Hyp2 := fresh in (
			assert (Hyp2 := PerpendicularDownPerpendicular l1 A H);
				fold l2 in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : ~OnLine l1 A);
	[try immediate  | pose (l2 := PerpendicularDown l1 A H);
		let Hyp1 := fresh in (
			assert (Hyp1 := PerpendicularDownOnLine l1 A H);
			let Hyp2 := fresh in (
				assert (Hyp2 := PerpendicularDownPerpendicular l1 A H);
					fold l2 in Hyp1, Hyp2))])
end.

(* Soit "l2" la droite poerepndiculaire a "l1" dressee du point "A" de "l1". *)

Ltac setPerpendicularUp l1 A l2 := match goal with
| H : OnLine l1 A |- _ => 
	pose (l2 := PerpendicularUp l1 A H);
	let Hyp1 := fresh in (
		assert (Hyp1 := PerpendicularUpOnLine l1 A H);
		let Hyp2 := fresh in (
			assert (Hyp2 := PerpendicularUpPerpendicular l1 A H);
				fold l2 in Hyp1, Hyp2))
| _ => let H := fresh in (
	assert (H : OnLine l1 A);
	[try immediate | pose (l2 := PerpendicularUp l1 A H);
		let Hyp1 := fresh in (
			assert (Hyp1 := PerpendicularUpOnLine l1 A H);
			let Hyp2 := fresh in (
				assert (Hyp2 := PerpendicularUpPerpendicular l1 A H);
					fold l2 in Hyp1, Hyp2))])
end.

(* Soit "l2" la droite parallele a "l1" passant par "A". *)

Ltac setParallel l1 A l2 := match goal with
	| H : ~OnLine l1 A |- _ => 
		pose (l2 := Parallel l1 A H);
		let Hyp1 := fresh in (
			assert (Hyp1 := OnLineAParallel l1 A H);
			let Hyp2 := fresh in (
				assert (Hyp2 :=  ParallelParallelLine l1 A H);
				fold l2 in Hyp1, Hyp2))
	| _ => let H := fresh in (
			assert (H : ~OnLine l1 A);
			[try immediate | pose (l2 := Parallel l1 A H);
				let Hyp1 := fresh in (
					assert (Hyp1 := OnLineAParallel l1 A H);
					let Hyp2 := fresh in (
						assert (Hyp2 :=  ParallelParallelLine l1 A H);
						fold l2 in Hyp1, Hyp2))])
end.
