Require Import A1_Plan A2_Orientation A3_Metrique A4_Droite A5_Cercle A7_Tactics .
Require Import B2_CollinearProp B3_EquiOrientedProp B4_RaysProp B5_BetweenProp B6_EquiDirectedProp B7_Tactics .
Require Import C1_Distance C2_CircleAndDistance C3_SumDistance C4_DistanceLe C5_TriangularInequality C6_DistanceTimesN C7_Tactics .
Require Import D1_IntersectionCirclesProp D3_SecondDimension D4_DistanceLt D5_Tactics .
Require Import E1_IntersectionLinesProp E2_NotEquidirectedIntersection E3_FourPointsIntersection.

Ltac setInterLinesPoint4 l1 l2 M := match goal with
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
			[idtac |
				pose (M := InterLinesPoint l1 l2 H);
				let Hyp1 := fresh in (
					assert (Hyp1 := OnLine1InterLinesPoint l1 l2 H);
					let Hyp2 := fresh in (
						assert (Hyp2 := OnLine2InterLinesPoint l1 l2 H);
						fold M in Hyp1, Hyp2))])
end.

Ltac setNotEquiDirectedInterPoint4 A B C D E := match goal with
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
	[try immediate3 | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
				fold E in Hyp1, Hyp2))])
|  H1 : Clockwise A B D |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise A B C);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
				fold E in Hyp1, Hyp2))])
|  H1 : Clockwise C D A |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise C D B);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
				fold E in Hyp1, Hyp2))])
|  H1 : Clockwise C D B |- _ => let H2 := fresh in (
	assert (H2 : ~Clockwise C D A);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
				fold E in Hyp1, Hyp2))])

|  H2 : ~Clockwise A B D |- _ => let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
				fold E in Hyp1, Hyp2))])
|  H2 : ~Clockwise A B C |- _ =>  let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
		let Hyp1 := fresh in (
			assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp2 :=fresh in (
				assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
				fold E in Hyp1, Hyp2))])
|  H2 : ~Clockwise C D B |- _ =>  let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[try immediate3 | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
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
	[immediate3 | let H2 := fresh in (
		assert (H2 : ~Clockwise A B D);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
					fold E in Hyp1, Hyp2))])])
	| let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[immediate3 | let H2 := fresh in (
		assert (H2 : ~Clockwise A B C);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
					fold E in Hyp1, Hyp2))])])
	| let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[immediate3 | let H2 := fresh in (
		assert (H2 : ~Clockwise C D B);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
					fold E in Hyp1, Hyp2))])])
	| let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[immediate3 | let H2 := fresh in (
		assert (H2 : ~Clockwise C D A);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D B A (FourPointsSecantLine C D B A H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D B A (FourPointsSecantLine C D B A H1 H2));
					fold E in Hyp1, Hyp2))])])

	| let H2 := fresh in (
	assert (H2 : ~Clockwise A B D);
	[immediate3 | let H1 := fresh in (
		assert (H1 : Clockwise A B C);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint A B C D (FourPointsSecantLine A B C D H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B C D (FourPointsSecantLine A B C D H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B C D (FourPointsSecantLine A B C D H1 H2));
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : ~Clockwise A B C);
	[immediate3 | let H1 := fresh in (
		assert (H1 : Clockwise A B D);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint A B D C (FourPointsSecantLine A B D C H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB A B D C (FourPointsSecantLine A B D C H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD A B D C (FourPointsSecantLine A B D C H1 H2));
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : ~Clockwise C D B);
	[immediate3 | let H1 := fresh in (
		assert (H1 : Clockwise C D A);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint C D A B (FourPointsSecantLine C D A B H1 H2));
			let Hyp1 := fresh in (
				assert (Hyp1 := NotEquiDirectedInterPointCollinearAB C D A B (FourPointsSecantLine C D A B H1 H2));
				let Hyp2 :=fresh in (
					assert (Hyp2 := NotEquiDirectedInterPointCollinearCD C D A B (FourPointsSecantLine C D A B H1 H2));
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : ~Clockwise C D A);
	[immediate3 | let H1 := fresh in (
		assert (H1 : Clockwise C D B);
		[try immediate3 | pose (E := NotEquiDirectedInterPoint C D B A (FourPointsSecantLine C D B A H1 H2));
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

Ltac setFourPointsInter4 A B C D E := match goal with
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
	[try immediate3 |
		pose (E := FourPointsInterPoint A B C D H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise B A D |- _ => let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[try immediate3 |
		pose (E := FourPointsInterPoint A B C D H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
				fold E in Hyp1, Hyp2))])

|  H1 : Clockwise A B D |- _ => let H2 := fresh in (
	assert (H2 : Clockwise B A C);
	[try immediate3 |
		pose (E := FourPointsInterPoint A B D C H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise B A C |- _ => let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[try immediate3 |
		pose (E := FourPointsInterPoint A B D C H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
				fold E in Hyp1, Hyp2))])

|  H1 : Clockwise C D A |- _ => let H2 := fresh in (
	assert (H2 : Clockwise D C B);
	[try immediate3 |
		pose (E := FourPointsInterPoint C D A B H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise D C B |- _ => let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[try immediate3 |
		pose (E := FourPointsInterPoint C D A B H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
				fold E in Hyp1, Hyp2))])

|  H1 : Clockwise C D B |- _ => let H2 := fresh in (
	assert (H2 : Clockwise D C A);
	[try immediate3 |
		pose (E := FourPointsInterPoint C D B A H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
				fold E in Hyp1, Hyp2))])
|  H2 : Clockwise D C A |- _ => let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[try immediate3 |
		pose (E := FourPointsInterPoint C D B A H1 H2);
		let Hyp1 := fresh in (
			assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
			let Hyp2 :=fresh in (
				assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
				fold E in Hyp1, Hyp2))])
|  |- _ => first
	[ let H1 := fresh in (
	assert (H1 : Clockwise A B C);
	[immediate3 |
		let H2 := fresh in (
		assert (H2 : Clockwise B A D);
		[try immediate3 |
			pose (E := FourPointsInterPoint A B C D H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise B A D);
	[immediate3 |
		let H1 := fresh in (
		assert (H1 : Clockwise A B C);
		[try immediate3 |
			pose (E := FourPointsInterPoint A B C D H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B C D H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B C D H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H1 := fresh in (
	assert (H1 : Clockwise A B D);
	[immediate3 |
		let H2 := fresh in (
		assert (H2 : Clockwise B A C);
		[try immediate3 |
			pose (E := FourPointsInterPoint A B D C H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise B A C);
	[immediate3 |
		let H1 := fresh in (
		assert (H1 : Clockwise A B D);
		[try immediate3 |
			pose (E := FourPointsInterPoint A B D C H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB A B D C H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD A B D C H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H1 := fresh in (
	assert (H1 : Clockwise C D A);
	[immediate3 |
		let H2 := fresh in (
		assert (H2 : Clockwise D C B);
		[try immediate3 |
			pose (E := FourPointsInterPoint C D A B H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise D C B);
	[immediate3 |
		let H1 := fresh in (
		assert (H1 : Clockwise C D A);
		[try immediate3 |
			pose (E := FourPointsInterPoint C D A B H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D A B H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D A B H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H1 := fresh in (
	assert (H1 : Clockwise C D B);
	[immediate3 |
		let H2 := fresh in (
		assert (H2 : Clockwise D C A);
		[try immediate3 |
			pose (E := FourPointsInterPoint C D B A H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
					fold E in Hyp1, Hyp2))])])
	|  let H2 := fresh in (
	assert (H2 : Clockwise D C A);
	[immediate3 |
		let H1 := fresh in (
		assert (H1 : Clockwise C D B);
		[try immediate3 |
			pose (E := FourPointsInterPoint C D B A H1 H2);
			let Hyp1 := fresh in (
				assert (Hyp1 := FourPointsInterPointCollinearAB C D B A H1 H2);
				let Hyp2 :=fresh in (
					assert (Hyp2 := FourPointsInterPointBetweenCD C D B A H1 H2);
					fold E in Hyp1, Hyp2))])])]
end.

Ltac immCollinear4 := match goal with
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

	| |- Collinear ?A _ _ => unfold A; immCollinear4
	| |- Collinear _ ?B _ => unfold B; immCollinear4
	| |- Collinear _ _ ?C => unfold C; immCollinear4
end.

Ltac immEquiOriented4 := match goal with
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

	| |- EquiOriented (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ _ _ => assert (FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2
	| |- EquiOriented _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ _ => assert (FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2
	| |- EquiOriented _ _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) _ => assert (FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2
	| |- EquiOriented _ _ _ (FourPointsInterPoint ?A ?B ?C ?D ?H ?H0) => assert (FourPointsInterPointBetweenCD A B C D H H0); immEquiOriented2

	| |- EquiOriented ?A _ _ _ => unfold A; immEquiOriented4
	| |- EquiOriented _ ?A _ _ => unfold A; immEquiOriented4
	| |- EquiOriented _ _ ?A _ => unfold A; immEquiOriented4
	| |- EquiOriented _ _ _ ?A => unfold A; immEquiOriented4
end.

Ltac immBetween4 :=  match goal with
	| H : Between ?A ?B ?C |- Between ?A ?B ?C => exact H
	| H : Between ?C ?B ?A |- Between ?A ?B ?C => apply (BetweenSym _ _ _ H)

	| |- Between ?C (FourPointsInterPoint _ _ ?C ?D _ _) ?D => apply FourPointsInterPointBetweenCD
	| |- Between ?D (FourPointsInterPoint _ _ ?C ?D _ _) ?C => apply BetweenSym; apply FourPointsInterPointBetweenCD

	| |- Between _ ?B _ => unfold B; immBetween4
end.

Ltac immSegment4 := match goal with
	| |- Segment ?A ?B ?A => apply SegmentABA
	| |- Segment ?A ?B ?B => apply SegmentABB
	| |- Segment Oo (DistancePlus?A ?B) ?A => apply IsDistanceSegmentDistancePlus; immIsDistance2 A

	| H : Segment ?A ?B ?C |- Segment ?A ?B ?C => exact H
	| H : Segment ?A ?B ?C |- Segment ?B ?A ?C => apply (SegmentSym _ _ _ H)

	| H : EquiOriented ?A ?B ?B ?C |- Segment ?A ?C ?B => apply (EquiOrientedSegment A B C H)
	| H : EquiOriented ?A ?B ?B ?C |- Segment ?C ?A ?B =>  apply SegmentSym; apply (EquiOrientedSegment A B C H)

	|  |- Segment _ _ _  => apply BetweenSegment; immBetween4
	| |- Segment _ _ _  =>  apply SegmentSym; apply BetweenSegment ; immBetween4

	| H : DistanceLe ?A ?B |- Segment Oo ?B ?A => exact H
end.

Ltac immNotEquiDirected4 := match goal with
	| H : ~EquiDirected ?A ?B ?C ?D |- ~EquiDirected ?A ?B ?C ?D => exact H
	| H : ~EquiDirected _ _ _ _  |- ~EquiDirected _ _ _ _  => contrapose0 H; immEquiDirected1
	| H : EquiDirected _ _ _ _  -> False |- ~EquiDirected _ _ _ _  => contrapose0 H; immEquiDirected1
	| H : ~Collinear _ _ _  |- ~EquiDirected _ _ _ _ => contrapose0 H; immCollinear1
	| H : Collinear _ _ _  -> False |- ~EquiDirected _ _ _ _ => contrapose0 H; immCollinear1

	|  |- ~EquiDirected _ _ _ _ => apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedPermutCD; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedPermutCD; apply  NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]

	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply NotEquiDirectedPermutCD; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]
	|  |- ~EquiDirected _ _ _ _ => apply NotEquiDirectedSym; apply NotEquiDirectedPermutCD; apply  NotEquiDirectedPermutAB; apply FourPointsSecantLine; [immClockwise1 | immNotClockwise3]

end.

Ltac immOnLine4 := match goal with
	| H : OnLine ?d ?A |- OnLine ?d ?A => exact H
	| |- OnLine ?d (LineA ?d) => destruct d; simpl; immediate3
	| |- OnLine ?d (LineB ?d) => destruct d; simpl; immediate3
	| |- OnLine (Ruler _ _ _) _ => simpl; immediate3
	| |- OnLine ?d (InterLinesPoint ?d _ _) => apply OnLine1InterLinesPoint
	| |- OnLine ?d (InterLinesPoint _ ?d _) => apply OnLine2InterLinesPoint
	| |- OnLine ?d _ => unfold d; simpl; immediate3
end.

Ltac immSecantLines4 := match goal with
	| |- SecantLines _ _ => simplLine1; immNotEquiDirected4
	| |- SecantLines _ _ => apply SecantLinesSym; simplLine1; immNotEquiDirected4
end.

Ltac solveEq4 := match goal with
	| |- ?X = ?X => apply refl_equal
	| H : ?X = ?Y |- ?X = ?Y => exact H
	| H : ?Y = ?X |- ?X = ?Y => rewrite H; apply refl_equal

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle3 | immOnCircle3 | immNotClockwise3]
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M); [immOnCircle3 | immOnCircle3 | immNotClockwise3]

	| |- ?M = InterLinesPoint ?l1 ?l2 ?H => apply (UniqueInterLinesPoint l1 l2 H M); immOnLine4
	| |- InterLinesPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueInterLinesPoint l1 l2 H M); immOnLine4

	| |- ?M = NotEquiDirectedInterPoint ?l1 ?l2 ?H => apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); immCollinear4
	| |- NotEquiDirectedInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); immCollinear4

	| |- ?M = FourPointsInterPoint ?l1 ?l2 ?H => apply (UniqueFourPointsInterPoint l1 l2 H M); immCollinear4
	| |- FourPointsInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueFourPointsInterPoint l1 l2 H M); immCollinear4

	| |- ?X = _ => unfold X; solveEq4
	| |- _ = ?Y => unfold Y; solveEq4
end.

Ltac immediate4 := match goal with 
	| |- True => trivial
	| H : False |- _ => elim H
	| H : ?X  |- ?X => exact H

	| |- ?A /\ ?B => split; immediate4
	| |- ?A \/ ?B => (left; immediate4)  || (right; immediate4)

	| |- DistancePlus _ _ = _ => solveDistance2
	| |- _ = DistancePlus _ _ => solveDistance2

	| |- DistanceTimes _ _ _ = _ => solveDistance2
	| |- _ = DistanceTimes _ _ _ => solveDistance2

	| |- Distance _ _ = _ => solveDistance2
	| |- _ = Distance _ _ => solveDistance2

	| |- IsDistance ?d => immIsDistance2 d

	| |- _ = _ => solveEq4
	| |- _ <> _ => immDistinct3
	| |- ?A = ?B -> False => fold(A <> B); immDistinct3

	| |- Clockwise _ _ _ => immClockwise1
	| |- ~Clockwise _ _ _  => immNotClockwise3
	| |- Clockwise ?A ?B ?C -> False  => fold (~Clockwise A B C); immNotClockwise3

	| |- Collinear _ _ _ => immCollinear4
	| |- ~Collinear _ _ _  => immNotCollinear1
	| |- Collinear ?A ?B ?C -> False  => fold (~Collinear A B C); immNotCollinear1

	| |- EquiOriented _ _ _ _ => immEquiOriented4
	| |- OpenRay _ _ _ => immOpenRay3
	| |- ClosedRay _ _ _ => immClosedRay3
	| |- Between _ _ _ => immBetween4
	| |- Segment _ _ _ => immSegment4

	| |- EquiDirected _ _ _ _ => immEquiDirected1
	| |- ~EquiDirected _ _ _ _ => immNotEquiDirected4
	| |- EquiDirected ?A ?B ?C ?D  -> False =>fold (~EquiDirected A B C D); immNotEquiDirected4

	| |- DistanceLe _ _ => immDistanceLe2
	| |- DistanceLt _ _ => immDistanceLt3

	| |- TriangularInequality _ _ _ _ _ _  => immTriangularInequality3
	| |- TriangleSpec _ _ _ _ _ _ => immTriangleSpec3

	| |- Diameter _ _ => immDiameter2
	| |- SecantLines _ _ => immSecantLines4

	| |- OnCircle _ _ => immOnCircle3
	| |- OnLine _ _ => immOnLine4
end.

Ltac byDefEqPoint4 := match goal with
	| |- ?X = ?X => apply refl_equal

	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); try immediate4
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M);try immediate4

	| |- ?M = InterLinesPoint ?l1 ?l2 ?H => apply (UniqueInterLinesPoint l1 l2 H M); try immOnLine4
	| |- ?M = NotEquiDirectedInterPoint ?l1 ?l2 ?H => apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); try immCollinear4
	| |- ?M = FourPointsInterPoint ?l1 ?l2 ?H => apply (UniqueFourPointsInterPoint l1 l2 H M); try immCollinear4

	| |-  InterLinesPoint ?l1 ?l2 ?H = ?M => rewrite sym_eq; apply (UniqueInterLinesPoint l1 l2 H M); try immOnLine4
	| |- NotEquiDirectedInterPoint ?l1 ?l2 ?H = ?M => rewrite sym_eq; apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); try immCollinear4
	| |- FourPointsInterPoint ?l1 ?l2 ?H = ?M => rewrite sym_eq; apply (UniqueFourPointsInterPoint l1 l2 H M); try immCollinear4
end.

Ltac stepEq4 X Y H  := match type of H with
	| Point => apply trans_eq with (y:=H); unfold H; byDefEqPoint4

	| OnCircle ?c ?A  => simplCircleHyp2 H; try solveDist2

	| SecantCircles ?c1 ?c2 => apply (EqPointsIntersectionCircles c1 c2 H); try immediate4
	| SecantLines ?l1 ?l2 => apply (EqPointsInterLines l1 l2 H X Y); try immediate4
	| ~EquiDirected ?A ?B ?C ?D => apply (EqPointsNotEquiDirectedInter A B C D X Y H); try immediate4

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

	| X = ?Z => rewrite H; try solveEq4
	| Y = ?Z => rewrite H; try solveEq4
	| ?Z = X => rewrite <- H; try solveEq4
	| ?Z = Y => rewrite <- H; try solveEq4
	| ?Z = ?T => first 
			[let Hyp := fresh in (assert (Hyp : X=Z); [solveEq4 | rewrite Hyp; clear Hyp; rewrite H; try solveEq4]) |
			let Hyp := fresh in (assert (Hyp : Y=Z); [solveEq4 | rewrite Hyp ; clear Hyp; rewrite H; try solveEq4]) |
			let Hyp := fresh in (assert (Hyp : X=T); [solveEq4 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq4]) |
			let Hyp := fresh in (assert (Hyp : Y=T); [solveEq4 | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq4])]
end.

Ltac step4 H := match goal with
	| |- DistancePlus _ _  = _ => stepEqDistance2 H
	| |- _ = DistancePlus _ _  => stepEqDistance2 H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance2 H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance2 H
	| |- Distance _ _ = _ => stepEqDistance2 H
	| |- _ = Distance _ _ => stepEqDistance2 H

	| |- DistanceLe _ _  => stepDistanceLe2 H
	| |- DistanceLt _ _  => stepDistanceLt3 H

	| |- _ = H => try unfold H; byDefEqPoint4
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint4

	| |- ?A = ?B => stepEq4 A B H
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

Ltac since4 txt := assert txt; try immediate4.

Ltac from4 H txt := assert txt; [(step4 H ; try immediate4) |  try immediate4].

Ltac as4 txt := let Hyp := fresh in
	(assert (Hyp : txt); [immediate4 | (step4 Hyp; try immediate4)]).
