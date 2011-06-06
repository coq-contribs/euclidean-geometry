Load "Tactics1_Immediate.v".

Ltac foldDistanceIn H := repeat 
match type of H with
| context[(Distance ?A ?B)] =>  try rewrite (DistanceSym B A); 
		let delta := fresh "delta" in (pose (delta := Distance A B); fold delta; fold delta in H)
end.

Ltac foldDistanceTimesIn H := 
simpl DistanceTimes; 
repeat (match type of H with
| context [(DistanceTimes ?n ?A ?B)] => try rewrite (DistanceTimesSym n B A);
		let delta := fresh "delta" in (pose (delta := DistanceTimes n A B); fold delta; fold delta in H)
| context[(Distance ?A ?B)] =>  try rewrite (DistanceSym B A); 
		let delta := fresh "delta" in (pose (delta := Distance A B); fold delta; fold delta in H)
end).

Ltac writeDistancePlusIn A B sigma := repeat
match goal with
	| |- context [(DistancePlus A B)] => fold sigma
	| |- context [(DistancePlus B A)] =>  rewrite (DistancePlusCommut B A); fold sigma
	| |- context [(DistancePlus A (DistancePlus B ?X))] => rewrite (DistancePlusAssoc A B X); fold sigma
	| |- context [(DistancePlus B (DistancePlus A ?X))] => rewrite (DistancePlusAssoc B A X); rewrite (DistancePlusCommut B A); fold sigma
	| |- context [(DistancePlus A ?X)] => headDistancePlus B X; rewrite (DistancePlusAssoc A B); fold sigma
	| |- context [(DistancePlus B ?X)] => headDistancePlus A X; rewrite (DistancePlusAssoc B A);  rewrite (DistancePlusCommut B A); fold sigma
end.

Ltac foldDistancePlusRecIn H A B := match B with
	| DistancePlus ?C ?D => foldDistancePlusRecIn H C D
	| _ => let sigma := fresh "sigma" in (pose (sigma := DistancePlus A B); writeDistancePlusIn A B sigma; fold sigma in H)
end.

Ltac foldDistancePlusIn H := 
repeat (match type of H with
| context [(DistancePlus ?A ?B)] => foldDistancePlusRecIn H A B
end).

Ltac substDistanceIn H := rewrite H || rewrite <- H.

Ltac unfoldDistanceIn H := 
match type of H with
| ?X = ?Y =>  generalize H; clear H; try subst X; try subst Y; intro H
end. 

Ltac unfoldRec X :=
match X with
| DistancePlus ?L ?R => unfoldRec L || unfoldRec R
| _ => subst X
end.

Ltac unfoldDistancePlusIn H := repeat
match type of H with
| ?X = ?Y =>   generalize H; (unfoldRec X || unfoldRec Y); clear H; intro H
end. 

Ltac stepEqDistance H  := 

(* H fournit une egalite de distance que l'on utilise comme reecriture*)

 repeat rewrite <- DistancePlusAssoc;
 repeat rewrite <- DistancePlusAssoc in H;
match type of H with

(* H peut etre  sous forme d'egalite *)

	| DistancePlus _ _  = _ => foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| _ = DistancePlus _ _  => foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| DistanceTimes _ _ _  = _ => foldDistanceTimesIn H; substDistanceIn H; unfoldDistanceIn H
	| _ = DistanceTimes _ _ _  => foldDistanceTimesIn H; substDistanceIn H; unfoldDistanceIn H
	| Distance _ _ = _ => foldDistanceIn H; substDistanceIn H; unfoldDistanceIn H
	| _ = Distance _ _ => foldDistanceIn H; substDistanceIn H; unfoldDistanceIn H

(* H peut etre  sous forme d'appartenancce a un cercle *)

	| OnLine (MidLine ?A ?B ?Hab) ?C => generalize (OnMidLineEqDistance A B Hab C H); intro

	| OnCircle (Compass _ _ _) _  => unfold OnCircle in H; foldDistanceIn H; substDistanceIn H; unfoldDistanceIn H
	| OnCircle ?c _  => unfold c, OnCircle in  H; foldDistanceIn H; substDistanceIn H; unfoldDistanceIn H

(* H peut etre  sous forme d'une propriete d'un triangle *)

	| Isosceles1 (Tr _ _ _) => generalize H; intro; simpl in H;  foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| Isosceles2 (Tr _ _ _) => generalize H; intro; simpl in H;  foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| Isosceles3 (Tr _ _ _) => generalize H; intro; simpl in H;  foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| Isosceles1 ?t => generalize H; intro; unfold t in H; simpl in H; foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| Isosceles2 ?t => generalize H; intro; unfold t in H; simpl in H; foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H
	| Isosceles3 ?t => generalize H; intro; unfold t in H; simpl in H; foldDistanceIn H;  foldDistanceTimesIn H; foldDistancePlusIn H; substDistanceIn H; unfoldDistanceIn H; unfoldDistancePlusIn H

	| Equilateral (Tr ?A ?B ?C) => 
		let Hyp := fresh in (assert  (Hyp := EquilateralEqSides12 A B C H); foldDistanceIn Hyp;  foldDistanceTimesIn Hyp; foldDistancePlusIn Hyp; substDistanceIn Hyp; unfoldDistanceIn Hyp; unfoldDistancePlusIn Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := EquilateralEqSides23 A B C H); foldDistanceIn Hyp;  foldDistanceTimesIn Hyp; foldDistancePlusIn Hyp; substDistanceIn Hyp; unfoldDistanceIn Hyp; unfoldDistancePlusIn Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := EquilateralEqSides31 A B C H);foldDistanceIn Hyp;  foldDistanceTimesIn Hyp; foldDistancePlusIn Hyp; substDistanceIn Hyp; unfoldDistanceIn Hyp; unfoldDistancePlusIn Hyp) 
	| Equilateral ?t => unfold t in H; stepEqDistance H

(* H peut etre  sous forme d'egalite de deux triangles*)

	| TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) => 	
		let Hyp := fresh in (assert  (Hyp := TCongruentEqSidesAB A B C D E F H);  foldDistanceIn Hyp;  foldDistanceTimesIn Hyp; foldDistancePlusIn Hyp; substDistanceIn Hyp; unfoldDistanceIn Hyp; unfoldDistancePlusIn Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := TCongruentEqSidesBC A B C D E F H);  foldDistanceIn Hyp;  foldDistanceTimesIn Hyp; foldDistancePlusIn Hyp; substDistanceIn Hyp; unfoldDistanceIn Hyp; unfoldDistancePlusIn Hyp)  ||
		let Hyp := fresh in (assert  (Hyp := TCongruentEqSidesCA A B C D E F H);  foldDistanceIn Hyp;  foldDistanceTimesIn Hyp; foldDistancePlusIn Hyp; substDistanceIn Hyp; unfoldDistanceIn Hyp; unfoldDistancePlusIn Hyp) 
	| TCongruent ?t1 _ => unfold t1; stepEqDistance H
	| TCongruent _ ?t2 => unfold t2; stepEqDistance H

	| _ = _ => rewrite H || rewrite <- H
end; try immediate.

Ltac stepDistanceLe H := match type of H with

(* deux distnaces egales sont dans le meme ordre de comparaison avec une troisieme distance *)

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

(* l'ordre est transitive *)

	| DistanceLe ?A ?B => match goal with
		| |- DistanceLe A ?C => apply (DistanceLeTrans A B C H); try immediate
		| |- DistanceLe ?C B => apply (DistanceLeTrans C A B C); [try immediate | exact H]
		end
end.

Ltac stepDistanceLt H := match type of H with

(* deux distnaces egales sont dans le meme ordre de comparaison avec une troisieme distance *)

	| Distance ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLt (Distance A B) _ => rewrite H
		| |- DistanceLt (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt _ (Distance A B) => rewrite H
		| |- DistanceLt _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt (Distance C D) _ => rewrite <- H
		| |- DistanceLt (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLt _ (Distance C D) => rewrite <- H
		| |- DistanceLt _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| DistancePlus ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLt (DistancePlus A B) _ => rewrite H
		| |- DistanceLt (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt _ (DistancePlus A B) => rewrite H
		| |- DistanceLt _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt (Distance C D) _ => rewrite <- H
		| |- DistanceLt (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLt _ (Distance C D) => rewrite <- H
		| |- DistanceLt _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| Distance ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLt (Distance A B) _ => rewrite H
		| |- DistanceLt (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt _ (Distance A B) => rewrite H
		| |- DistanceLt _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLt (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLt _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLt _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistancePlus ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLt (DistancePlus A B) _ => rewrite H
		| |- DistanceLt (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt _ (DistancePlus A B) => rewrite H
		| |- DistanceLt _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLt (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLt _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLt _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistanceTimes ?n ?A ?B = Distance ?C ?D => match goal with
		| |- DistanceLt (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLt (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLt _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt (Distance C D) _ => rewrite <- H
		| |- DistanceLt (Distance D C) _ => rewrite (DistanceSym D C); rewrite <- H
		| |- DistanceLt _ (Distance C D) => rewrite <- H
		| |- DistanceLt _ (Distance D C) => rewrite (DistanceSym D C); rewrite <- H
		end
	| Distance ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLt (Distance A B) _ => rewrite H
		| |- DistanceLt (Distance B A) _ => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt _ (Distance A B) => rewrite H
		| |- DistanceLt _ (Distance B A) => rewrite (DistanceSym B A); rewrite H
		| |- DistanceLt (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLt (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLt _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLt _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
	| DistanceTimes ?n ?A ?B = DistancePlus ?C ?D => match goal with
		| |- DistanceLt (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLt (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLt _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt (DistancePlus C D) _ => rewrite <- H
		| |- DistanceLt (DistancePlus D C) _ => rewrite (DistancePlusCommut D C); rewrite <- H
		| |- DistanceLt _ (DistancePlus C D) => rewrite <- H
		| |- DistanceLt _ (DistancePlus D C) => rewrite (DistancePlusCommut D C); rewrite <- H
		end
	| DistancePlus ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLt (DistancePlus A B) _ => rewrite H
		| |- DistanceLt (DistancePlus B A) _ => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt _ (DistancePlus A B) => rewrite H
		| |- DistanceLt _ (DistancePlus B A) => rewrite (DistancePlusCommut B A); rewrite H
		| |- DistanceLt (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLt (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLt _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLt _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
	| DistanceTimes ?n ?A ?B = DistanceTimes ?n ?C ?D => match goal with
		| |- DistanceLt (DistanceTimes n A B) _ => rewrite H
		| |- DistanceLt (DistanceTimes n B A) _ => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt _ (DistanceTimes n A B) => rewrite H
		| |- DistanceLt _ (DistanceTimes n B A) => rewrite (DistanceTimesSym n B A);rewrite H
		| |- DistanceLt (DistanceTimes n C D) _ => rewrite <- H
		| |- DistanceLt (DistanceTimes n D C) _ => rewrite (DistanceTimesSym n D C);rewrite H
		| |- DistanceLt _ (DistanceTimes n C D) => rewrite <- H
		| |- DistanceLt _ (DistanceTimes n D C) => rewrite (DistanceTimesSym n D C);rewrite H
		end
end.

Ltac stepSupplement A B C D E F H := match type of H with 

(* deux angles supplementaires d'un meme troisieme sont egaux *)

	| Supplement A B C ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate
	| Supplement C B A ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate
	| Supplement ?K ?L ?M A B C => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate
	| Supplement ?K ?L ?M C B A => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate

	| Supplement D E F ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate
	| Supplement F E D ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate
	| Supplement ?K ?L ?M D E F => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate
	| Supplement ?K ?L ?M F E D => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate

(* deux angles egaux sont supplementaires d'un meme troisieme *)

	| CongruentAngle A B C ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate
	| CongruentAngle C B A ?K ?L ?M => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate
	| CongruentAngle ?K ?L ?M A B C => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate
	| CongruentAngle ?K ?L ?M C B A => apply (SupplementCongruentSupplement  K L M A B C D E F); try immediate

	| CongruentAngle D E F ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate
	| CongruentAngle F E D ?K ?L ?M => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate
	| CongruentAngle ?K ?L ?M D E F => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate
	| CongruentAngle ?K ?L ?M F E D => apply  SupplementSym; apply (SupplementCongruentSupplement  K L M D E F A B C); try immediate

(* l'angle nul et l'angle plat sont supplementaires *)

	| NullAngle A B C => apply NullElongatedSupplement; try immediate
	| NullAngle C B A => apply NullElongatedSupplement; try immediate
	| NullAngle D E F => apply  SupplementSym; apply NullElongatedSupplement; try immediate
	| NullAngle F E D => apply  SupplementSym; apply NullElongatedSupplement; try immediate

	| ElongatedAngle A B C => apply  SupplementSym; apply NullElongatedSupplement; try immediate
	| ElongatedAngle C B A => apply  SupplementSym; apply NullElongatedSupplement; try immediate
	| ElongatedAngle D E F =>  apply NullElongatedSupplement; try immediate
	| ElongatedAngle F E D => apply NullElongatedSupplement; try immediate
	
(* deux angles droits sont supplementaires*)

	| RightAngle _ _ _ =>  apply RightRightSupplement; try immediate

(* dans un parallelogramme, deux angles ayant un cote commun sont supplementaires*)

	| Parallelogramm ?X ?Y ?Z ?T  => match goal with
		| |- Supplement T X Y X Y Z => apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement Y X T X Y Z =>  apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement T X Y Z Y X => apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement Y X T Z Y X =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement X Y Z T X Y => apply SupplementSym; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement X Y Z Y X T => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement Z Y X T X Y => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate
		|  |- Supplement Z Y X Y X T => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammDABSupplementAngleABC X Y Z T H); try immediate

		|  |- Supplement X Y Z Y Z T => apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement Z Y X Y Z T =>  apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement X Y Z T Z Y => apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement Z Y X T Z Y =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement Y Z T X Y Z => apply SupplementSym; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement Y Z T Z Y X => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement T Z Y X Y Z => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate
		|  |- Supplement T Z Y Z Y X => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammABCSupplementAngleBCD X Y Z T H); try immediate

		|  |- Supplement Y Z T Z T X => apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement T Z Y Z T X =>  apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement Y Z T X T Z => apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement T Z Y X T Z =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement Z T X Y Z T => apply SupplementSym; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement Z T X T Z Y => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement X T Z Y Z T => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate
		|  |- Supplement X T Z T Z Y => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammBCDSupplementAngleCDA X Y Z T H); try immediate

		|  |- Supplement Z T X T X Y => apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement X T Z T X Y =>  apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement Z T X Y X T => apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement X T Z Y X T =>  apply SupplementRev2; apply SupplementRev1;apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement T X Y Z T X => apply SupplementSym; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement T X Y X T Z => apply SupplementSym; apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement Y X T Z T X => apply SupplementSym; apply SupplementRev2; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
		|  |- Supplement Y X T X T Z => apply SupplementSym; apply SupplementRev2;  apply SupplementRev1; apply (ParallelogrammCDASupplementAngleDAB X Y Z T H); try immediate
	end

end.

Ltac stepOpposed A B C D E H := match type of H  with

(* liste des cas selon l'orientation et l'alignement des cotes *)

	| ~Clockwise B A C => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	| ~Clockwise A C B => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise C B A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise A B C => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise B C A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise C A B => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate

	|  ~Clockwise D A E => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise A E D => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise E D A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise A D E => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise D E A => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise E A D => apply AntiClockwiseBetweenCongruentOpposedAngles; try immediate

	|  Clockwise B A C => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise A C B => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise C B A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise A B C => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise B C A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise C A B => apply ClockwiseBetweenCongruentOpposedAngles; try immediate

	|  Clockwise D A E => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise A E D=> apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  Clockwise E D A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise A D E => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise D E A => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
	|  ~Clockwise E A D => apply ClockwiseBetweenCongruentOpposedAngles; try immediate
end.

Ltac stepCongruentTransAngle A B C D E F H := match type of H with

(* l'egalite d'angles est transitive*)

		| CongruentAngle A B C ?X ?Y ?Z => apply (CongruentAngleTrans A B C X Y Z D E F H);  try immediate
		| CongruentAngle C B A ?X ?Y ?Z => apply CongruentAngleRev1;  apply (CongruentAngleTrans C B A X Y Z D E F H);  try immediate
		| CongruentAngle ?X ?Y ?Z  A B C => apply (CongruentAngleTrans  A B C X Y Z D E F (CongruentAngleSym X Y Z A B C H));  try immediate
		| CongruentAngle ?X ?Y ?Z  C B A =>  apply CongruentAngleRev1; apply (CongruentAngleTrans  C B A X Y Z D E F (CongruentAngleSym X Y Z C B A H));  try immediate
		
		| CongruentAngle D E F ?X ?Y ?Z => apply CongruentAngleSym; apply (CongruentAngleTrans D E F X Y Z A B C H);  try immediate
		| CongruentAngle F E D ?X ?Y ?Z => apply CongruentAngleSym; apply CongruentAngleRev1;  apply (CongruentAngleTrans F E D X Y Z A B C H);  try immediate
		| CongruentAngle ?X ?Y ?Z  D E F => apply CongruentAngleSym; apply (CongruentAngleTrans D E F X Y Z A B C (CongruentAngleSym X Y Z D E F H));  try immediate
		| CongruentAngle ?X ?Y ?Z  F E D =>  apply CongruentAngleSym; apply CongruentAngleRev1; apply (CongruentAngleTrans F E D X Y Z A B C (CongruentAngleSym X Y Z F E D H));  try immediate
end.

Ltac stepCongruentAngle A B C D E F H :=  match type of H with

(* deux angles sont egaux s'ils ont memes cotes *)

	| OpenRay B A D  => apply CongruentAngleSides; try immediate
	| OpenRay B A F  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| OpenRay B C D  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| OpenRay B C F  => apply CongruentAngleSides; try immediate
	| OpenRay B D A  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| OpenRay B F A  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| OpenRay B D C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| OpenRay B F C  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate

	| ClosedRay B A D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| ClosedRay B A F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| ClosedRay B C D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| ClosedRay B C F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| ClosedRay B D A  => apply CongruentAngleSides; try immediate
	| ClosedRay B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| ClosedRay B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| ClosedRay B F C  => apply CongruentAngleSides; try immediate

	| Segment B A D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| Segment B A F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment B C D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment B C F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| Segment B D A  => apply CongruentAngleSides; try immediate
	| Segment B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment B F C  => apply CongruentAngleSides; try immediate

	| Segment A B D  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| Segment A B F  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment C B D  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment C B F  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| Segment D B A  => apply CongruentAngleSides; try immediate
	| Segment F B A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment D B C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Segment F B C  => apply CongruentAngleSides; try immediate

	| Between B A D  =>apply CongruentAngleSides; try immediate
	| Between B A F  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between B C D  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between B C F  =>apply CongruentAngleSides; try immediate
	| Between B D A  => apply CongruentAngleSides; try immediate
	| Between B F A  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between B D C  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between B F C  => apply CongruentAngleSides; try immediate

	| Between A D B  =>apply CongruentAngleSides; try immediate
	| Between A F B  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between C D B  =>apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between C F B  =>apply CongruentAngleSides; try immediate
	| Between D A B  => apply CongruentAngleSides; try immediate
	| Between F A B  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between D C B  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| Between F C B  => apply CongruentAngleSides; try immediate

	| EquiOriented B A B D  => apply CongruentAngleSides; try immediate
	| EquiOriented B A B F  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| EquiOriented B C B D  => apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| EquiOriented B C B F  => apply CongruentAngleSides; try immediate
	| EquiOriented B D B A  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	| EquiOriented B F B A  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| EquiOriented B D B C  => apply CongruentAngleSym; apply CongruentAngleRev2; apply CongruentAngleSides; try immediate
	| EquiOriented B F B C  => apply CongruentAngleSym; apply CongruentAngleSides; try immediate
	
(* deux angles sont egaux s'ils sont egaux a un meme troisieme, s'ils sont nuls ou plats tous les deux*)

	| CongruentAngle _ _ _ _ _ _ => stepCongruentTransAngle A B C D E F H
	| NullAngle _ _ _ => apply (NullCongruentAngle A B C D E F) ; try immediate
	| ElongatedAngle _ _ _  => apply (ElongatedCongruentAngle A B C D E F) ; try immediate

(* deux angles opposes sont egaux *)
	
	| OpposedAngles  ?J ?K ?L ?M ?N => let Hyp := fresh in (
						assert (Hyp := OpposedCongruentAngles J K L M N H); 
						stepCongruentTransAngle A B C D E F Hyp)

(* deux angles correspondants dans deux triangles egaux sont egaux *)

	| TCongruent (Tr B A C)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A M K L);
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr B C A)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C M K L);
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr A B C)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C K L M);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr C B A)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A K L M);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr C A B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C L M K);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr A C B)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A L M K);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr B A C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L C B A );
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr B C A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L A B C );
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr A B C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M A B C);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr C B A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M C B A);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr A C B)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K C B A);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr C A B)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K A B C);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])

	| TCongruent (Tr E D F)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D M K L);
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr E F D)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F M K L);
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr D E F)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F K L M);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr F E D)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D K L M);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr D F E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D L M K);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr F D E)  (Tr ?K ?L ?M) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F L M K);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr E F D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L D E F );
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M) (Tr E D F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle M K L F E D );
			[ apply TCongruentAnglesA; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr D E F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M D E F);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent (Tr ?K ?L ?M)  (Tr F E D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle K L M F E D);
			[ apply TCongruentAnglesB; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr D F E)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K F E D);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])
	| TCongruent  (Tr ?K ?L ?M)  (Tr F D E)=> let Hyp := fresh in (
			assert (Hyp : CongruentAngle L M K D E F);
			[ apply TCongruentAnglesC; try immediate | stepCongruentAngle A B C D E F Hyp])

(* les deux angles a la base d'un triangle isocele sont egaux *)

	| Isosceles1 (Tr A B C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C A C B);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles1 (Tr C B A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A C A B);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles1 (Tr A C B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A C B A B C);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles1 (Tr C A B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C A B C B A);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])

	| Isosceles2 (Tr B A C) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle A C B A B C);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles2 (Tr B C A) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle C A B C B A);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles2 (Tr A C B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A C A B);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles2 (Tr C A B) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C A C B);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])

	| Isosceles3 (Tr B A C) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C B A C A B);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles3 (Tr B C A) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A B C A C B);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles3 (Tr A B C) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle C A B C B A);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles3 (Tr C B A) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle A C B A B C);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])

	| Isosceles1 (Tr D E F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F D F E);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles1 (Tr F E D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D F D E);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles1 (Tr D F E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D F E D E F);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles1 (Tr F D E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F D E F E D);
			[ apply IsoscelesEqAngles1; try immediate | stepCongruentAngle A B C D E F Hyp])

	| Isosceles2 (Tr E D F) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle D F E D E F);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles2 (Tr E F D) => let Hyp := fresh in (
			assert (Hyp : CongruentAngle F D E F E D);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles2 (Tr D F E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D F D E);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles2 (Tr F D E) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F D F E);
			[ apply IsoscelesEqAngles2; try immediate | stepCongruentAngle A B C D E F Hyp])

	| Isosceles3 (Tr E D F) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F E D F D E);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles3 (Tr E F D) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D E F D F E);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles3 (Tr D E F) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle F D E F E D);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])
	| Isosceles3 (Tr F E D) =>let Hyp := fresh in (
			assert (Hyp : CongruentAngle D F E D E F);
			[ apply IsoscelesEqAngles3; try immediate | stepCongruentAngle A B C D E F Hyp])

(* les trois angles d'un triangle equilateral sont egaux *)

	| Equilateral (Tr B A C) => assert (CongruentAngle A C B A B C); assert (CongruentAngle C B A C A B); try immediate
	| Equilateral (Tr B C A) => assert (CongruentAngle C A B C B A); assert (CongruentAngle A B C A C B); try immediate
	| Equilateral (Tr A B C) => assert (CongruentAngle A B C A C B); assert (CongruentAngle C A B C B A); try immediate
	| Equilateral (Tr C B A) => assert (CongruentAngle C B A C A B); assert (CongruentAngle A C B A B C); try immediate
	| Equilateral (Tr A C B) => assert (CongruentAngle A C B A B C); assert (CongruentAngle C B A C A B); try immediate
	| Equilateral (Tr C A B) => assert (CongruentAngle C A B C B A); assert (CongruentAngle A B C A C B); try immediate

	| Equilateral (Tr E D F) => assert (CongruentAngle D F E D E F); assert (CongruentAngle F E D F D E); try immediate
	| Equilateral (Tr E F D) => assert (CongruentAngle F D E F E D); assert (CongruentAngle D E F D F E); try immediate
	| Equilateral (Tr D E F) => assert (CongruentAngle D E F D F E); assert (CongruentAngle F D E F E D); try immediate
	| Equilateral (Tr F E D) => assert (CongruentAngle F E D F D E); assert (CongruentAngle D F E D E F); try immediate
	| Equilateral (Tr D F E) => assert (CongruentAngle D F E D E F); assert (CongruentAngle F E D F D E); try immediate
	| Equilateral (Tr F D E) => assert (CongruentAngle F D E F E D); assert (CongruentAngle D E F D F E); try immediate

(* deux angles supplementaires d'un meme troisieme sont egaux *)

	| Supplement A B C ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate
	| Supplement C B A ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate
	| Supplement ?K ?L ?M A B C => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate
	| Supplement ?K ?L ?M C B A => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate

	| Supplement D E F ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate
	| Supplement F E D ?K ?L ?M => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate
	| Supplement ?K ?L ?M D E F => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate
	| Supplement ?K ?L ?M F D E => apply (SupplementSupplementCongruent A B C D E F K L M); try immediate

(* dans un parallelogramme, les angles opposes sont egaux *)

	| Parallelogramm ?X ?Y ?Z ?T => match goal with
		| |- CongruentAngle T X Y Y Z T  => apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle Y X T Y Z T  => apply CongruentAngleRev1; apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle T X Y T Z Y  => apply CongruentAngleRev2; apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle Y X T T Z Y  => apply CongruentAngleRev; apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle Y Z T T X Y  => apply CongruentAngleSym; apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle Y Z T Y X T  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle T Z Y T X Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammDABeqBCD; try immediate
		| |- CongruentAngle T Z Y Y X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammDABeqBCD; try immediate

		| |- CongruentAngle X Y Z Z T X  => apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle Z Y X Z T X  => apply CongruentAngleRev1; apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle X Y Z X T Z  => apply CongruentAngleRev2; apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle Z Y X X T Z  => apply CongruentAngleRev; apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle Z T X X Y Z  => apply CongruentAngleSym; apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle Z T X Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle X T Z X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammABCeqCDA; try immediate
		| |- CongruentAngle X T Z Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammABCeqCDA; try immediate

		| |- CongruentAngle Y X Z T Z X  => apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle Z X Y T Z X  => apply CongruentAngleRev1; apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle Y X Z X Z T  => apply CongruentAngleRev2; apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle Z X Y X Z T  => apply CongruentAngleRev; apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle T Z X Y X Z  => apply CongruentAngleSym; apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle T Z X Z X Y  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle X Z T Y X Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammBACeqDCA; try immediate
		| |- CongruentAngle X Z T Z X Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammBACeqDCA; try immediate

		| |- CongruentAngle T X Z Y Z X  => apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle Z X T Y Z X  => apply CongruentAngleRev1; apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle T X Z X Z Y  => apply CongruentAngleRev2; apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle Z X T X Z Y  => apply CongruentAngleRev; apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle Y Z X T X Z  => apply CongruentAngleSym; apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle Y Z X Z X T  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle X Z Y T X Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammDACeqBCA; try immediate
		| |- CongruentAngle Z Z Y Z X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammDACeqBCA; try immediate

		| |- CongruentAngle X Y T Z T Y  => apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle T Y X Z T Y  => apply CongruentAngleRev1; apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle X Y T Y T Z  => apply CongruentAngleRev2; apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle T Y X Y T Z  => apply CongruentAngleRev; apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle Z T Y X Y T  => apply CongruentAngleSym; apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle Z T Y T Y X  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle Y T Z X Y T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammABDeqCDB; try immediate
		| |- CongruentAngle Y T Z T Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammABDeqCDB; try immediate

		| |- CongruentAngle X T Y Z Y T  => apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle Y T X Z Y T  => apply CongruentAngleRev1; apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle X T Y T Y Z  => apply CongruentAngleRev2; apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle Y T X T Y Z  => apply CongruentAngleRev; apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle Z Y T X T Y  => apply CongruentAngleSym; apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle Z Y T Y T X  => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle T Y Z X T Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammADBeqCBD; try immediate
		| |- CongruentAngle T Y Z Y T X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammADBeqCBD; try immediate

(* dans un parallelogramme, les angles exterieurs sont egaux *)

		| |- CongruentAngle T X Y Z Y ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y X T Z Y ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T X Y ?U Y Z => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y X T ?U Y Z => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z Y ?U T X Y => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  Z Y ?U Y X T => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Y Z  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Y Z  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle X Y Z T Z ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z Y X T Z ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X Y Z ?U Z T => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z Y X ?U Z T => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T Z ?U X Y Z => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  T Z ?U Z Y X => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Z T  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Z T  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle Y Z T X T ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T Z Y X T ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y Z T ?U T X => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T Z Y ?U T X => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X T ?U Y Z T => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  X T ?U T Z Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U T X  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U T X  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle Z T X Y X ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X T Z Y X ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z T X ?U X Y => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X T Z ?U X Y => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y X ?U Z T X => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  Y X ?U X T Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U X Y  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U X Y  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle Y X T Z T ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T X Y Z T ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y X T ?U T Z => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T X Y ?U T Z => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z T ?U Y X T => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  Z T ?U T X Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U T Z  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U T Z  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle X T Z Y Z ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z T X Y Z ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X T Z ?U Z Y => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z T X ?U Z Y => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y Z ?U X T Z => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  Y Z ?U Z T X => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Z Y  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Z Y  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle T Z Y X Y ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y Z T X Y ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T Z Y ?U Y X => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Y Z T ?U Y X => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X Y ?U T Z Y => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  X Y ?U Y Z T => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Y X  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U Y X  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

		| |- CongruentAngle Z Y X T X ?U => apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X Y Z T X ?U => apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle Z Y X ?U X T => apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle X Y Z ?U X T => apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle T X ?U Z Y X => apply CongruentAngleSym; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle  T X ?U X Y Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U X T  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply ParallelogrammExteriorAngles; try immediate
		| |- CongruentAngle ?U X T  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply ParallelogrammExteriorAngles; try immediate

(* dans un parallelogramme, les angles alterne-interne sont egaux *)

		| |- CongruentAngle T X Y ?U Y X => apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle Y X T ?U Y X => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle T X Y X Y ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle Y X T X Y ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle ?U Y X T X Y => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle  ?U Y X Y X T => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle X Y ?U  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate
		| |- CongruentAngle X Y ?U  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X Y Z T U); try immediate

		| |- CongruentAngle Z T X ?U X T => apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle X T Z ?U X T => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle Z T X T X ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle X T Z T X ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle ?U X T Z T X => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle  ?U X T X T Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle T X ?U  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate
		| |- CongruentAngle T X ?U  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T X Y Z U); try immediate

		| |- CongruentAngle Y Z T ?U T Z => apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle T Z Y ?U T Z => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle Y Z T Z T ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle T Z Y Z T ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle ?U T Z Y Z T => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle  ?U T Z T Z Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle Z T ?U  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate
		| |- CongruentAngle Z T ?U  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z T X Y U); try immediate

		| |- CongruentAngle X Y Z ?U Z Y => apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle Z Y X ?U Z Y => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle X Y Z Y Z ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle Z Y X Y Z ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle ?U Z Y X Y Z => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle  ?U Z Y Z Y X => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle Y Z ?U  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate
		| |- CongruentAngle Y Z ?U  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y Z T X U); try immediate

		| |- CongruentAngle Y X T ?U T X => apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle T X Y ?U T X => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle Y X T X T ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle T X Y X T ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle ?U T X Y X T => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle  ?U T X T X Y => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle X T ?U  Y X T  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate
		| |- CongruentAngle X T ?U  T X Y  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles X T Z Y U); try immediate

		| |- CongruentAngle Z Y X ?U X Y => apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle X Y Z ?U X Y => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle Z Y X Y X ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle X Y Z Y X ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle ?U X Y Z Y X => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle  ?U X Y X Y Z => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle Y X ?U  Z Y X  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate
		| |- CongruentAngle Y X ?U  X Y Z  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Y X T Z U); try immediate

		| |- CongruentAngle T Z Y ?U Y Z => apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle Y Z T ?U Y Z => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle T Z Y Z Y ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle Y Z T Z Y ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle ?U Y Z T Z Y => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle  ?U Y Z Y Z T => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle Z Y ?U  T Z Y  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate
		| |- CongruentAngle Z Y ?U  Y Z T  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles Z Y X T U); try immediate

		| |- CongruentAngle X T Z ?U Z T => apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle Z T X ?U Z T => apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle X T Z T Z ?U => apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle Z T X T Z ?U => apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle ?U Z T X T Z => apply CongruentAngleSym; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle  ?U Z T Z T X => apply CongruentAngleSym; apply CongruentAngleRev1; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle T Z ?U  X T Z  => apply CongruentAngleSym; apply CongruentAngleRev2; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate
		| |- CongruentAngle T Z ?U  Z T X  => apply CongruentAngleSym; apply CongruentAngleRev; apply (ParallelogrammAlternateAngles T Z Y X U); try immediate

	end

	| ?X = ?Y => rewrite H || rewrite <- H
end.

Ltac stepNullAngle A B C H :=  match type of H with

(* en utilisant la definition*)
	| _ <> _  => apply (OpenRayNullAngle B A C);  try immediate
	| OpenRay _ _ _  => apply (OpenRayNullAngle B A C);  try immediate
	| ClosedRay _ _ _  => apply (OpenRayNullAngle B A C);  try immediate

(* un angle egal a un angle nul est nul *)
	| NullAngle ?D ?E ?F => apply (CongruentNullAngle D E F A B C H); try immediate

	| CongruentAngle ?D ?E ?F A B C => apply (CongruentNullAngle D E F A B C); try immediate
	| CongruentAngle ?D ?E ?F C B A => apply (CongruentNullAngle D E F A B C); try immediate
	| CongruentAngle A B C ?D ?E ?F => apply (CongruentNullAngle D E F A B C); try immediate
	| CongruentAngle C B A ?D ?E ?F => apply (CongruentNullAngle D E F A B C); try immediate

(* un angle supplementaire d'un angle plat est nul *)
	| ElongatedAngle ?D ?E ?F => apply (ElongatedSupplementNull A B C D E F H); try immediate

	| Supplement A B C ?D ?E ?F => apply (ElongatedSupplementNull A B C D E F); try immediate
	| Supplement C B A ?D ?E ?F => apply (ElongatedSupplementNull A B C D E F); try immediate
	| Supplement ?D ?E ?F A B C => apply (ElongatedSupplementNull A B C D E F); try immediate
	| Supplement ?D ?E ?F C B A => apply (ElongatedSupplementNull A B C D E F); try immediate

end.

Ltac stepElongatedAngle A B C H :=  match type of H with

(* en utilisant la definition*)
	| ElongatedAngle ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C H); try immediate

	| Segment A C B => apply BetweenElongatedAngle; try immediate
	| Segment C A B => apply BetweenElongatedAngle; try immediate

(* un angle egal a un angle plat est plat *)

	| CongruentAngle ?D ?E ?F A B C => apply (CongruentElongatedAngle D E F A B C); try immediate
	| CongruentAngle ?D ?E ?F C B A => apply (CongruentElongatedAngle D E F A B C); try immediate
	| CongruentAngle A B C ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C); try immediate
	| CongruentAngle C B A ?D ?E ?F => apply (CongruentElongatedAngle D E F A B C); try immediate

(* un angle supplementaire d'un angle nul est plat *)

	| NullAngle ?D ?E ?F => apply (NullSupplementElongated D E F A B C H); try immediate

	| Supplement A B C ?D ?E ?F => apply (NullSupplementElongated D E F A B C); try immediate
	| Supplement C B A ?D ?E ?F => apply (NullSupplementElongated D E F A B C); try immediate
	| Supplement ?D ?E ?F A B C => apply (NullSupplementElongated D E F A B C); try immediate
	| Supplement ?D ?E ?F C B A => apply (NullSupplementElongated D E F A B C); try immediate
end.

Ltac stepRightAngle A B C H  := match goal with

(* un angle forme par deux droites perpendiculaires est droit *)

	| |- RightAngle A (PerpendicularPoint ?l1 ?l2 ?Hp) C => apply (PerpendicularRightAngle l1 l2 Hp A C); try immediate
	| _  => match type of H with

(* un angle egal ou supplementaire d'un angle droit est droit *)

		| RightAngle ?D ?E ?F => apply (RightOrRight D E F A B C); try immediate

(* un angle egal a un angle droit est droit *)

		| CongruentAngle ?D ?E ?F A B C => apply (CongruentRightAngle D E F A B C); try immediate
		| CongruentAngle ?D ?E ?F C B A => apply (CongruentRightAngle D E F A B C); try immediate
		| CongruentAngle A B C ?D ?E ?F => apply (CongruentRightAngle D E F A B C); try immediate
		| CongruentAngle C B A ?D ?E ?F => apply (CongruentRightAngle D E F A B C); try immediate

(* un angle supplementaire d'un angle droit est droit *)

		| Supplement ?D ?E ?F A B C => apply (OrSupplementRight D E F A B C); try immediate
		| Supplement ?D ?E ?F C B A => apply (OrSupplementRight D E F A B C); try immediate
		| Supplement A B C ?D ?E ?F => apply (OrSupplementRight D E F A B C); try immediate
		| Supplement C B A ?D ?E ?F => apply (OrSupplementRight D E F A B C); try immediate

(* un angle forme par la mediatrice d'un segment avec ce segment est droit *)

		| OnLine (MidLine A ?D ?H) C => apply (OnMidLineEqMidPointRightAngleA A D  B C H); try immediate
		| OnLine (MidLine ?D A ?H) C => apply (OnMidLineEqMidPointRightAngleB D A  B C H); try immediate
		| OnLine (MidLine C ?D ?H) A => apply RightAngleSym; apply (OnMidLineEqMidPointRightAngleA C D B A H); try immediate
		| OnLine (MidLine ?D C ?H) A => apply RightAngleSym; apply (OnMidLineEqMidPointRightAngleB D C B A H); try immediate

(* un angle forme par deux droites perpendiculaires est droit *)
	
		| Perpendicular ?l1 ?l2 => apply (PointsPerpendicularRightAngle A B C l1 l2 H); try immediate
	end
end.

Ltac byDefEqPoint := match goal with
	| |- ?X = ?X => apply refl_equal

(* le point "V" est le point unitaire sur l'axe des ordonnees*)
	| |- ?M = Vv => apply EqVv; [try solveDistance | try immNotClockwise | try solveDistance]	| |- Vv = ?M => apply sym_eq; apply EqVv; [try solveDistance | try immNotClockwise | try solveDistance]

(* point intersection de deux cercles *)
	| |- ?M = IntersectionCirclesPoint ?c1 ?c2 ?H => apply (UniqueIntersectionCirclesPoint c1 c2 H M); try immediate
	| |- IntersectionCirclesPoint ?c1 ?c2 ?H = ?M => apply sym_eq; apply (UniqueIntersectionCirclesPoint c1 c2 H M);try immediate

(* point intersection de deux droites *)
	| |- ?M = InterLinesPoint ?l1 ?l2 ?H => apply (UniqueInterLinesPoint l1 l2 H M); try immOnLine
	| |- InterLinesPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueInterLinesPoint l1 l2 H M); try immOnLine

	| |- ?M = NotEquiDirectedInterPoint ?l1 ?l2 ?H => apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); try immCollinear
	| |- NotEquiDirectedInterPoint ?l1 ?l2 ?H = ?M => apply sym_eq; apply (UniqueNotEquiDirectedInterPoint l1 l2 H M); try immCollinear

	| |- ?M = FourPointsInterPoint ?l1 ?l2 ?I3 ?I4 ?H1 ?H2  => apply (UniqueFourPointsInterPoint l1 l2 I3 I4 H1 H2 M); try immCollinear
	| |- FourPointsInterPoint?l1 ?l2 ?I3 ?I4 ?H1 ?H2 = ?M => apply sym_eq; apply (UniqueFourPointsInterPoint l1 l2 I3 I4 H1 H2 M); try immCollinear

(* point intersection d'une droite et d'un cercle *)
	| |- ?M = InterDiameterPoint ?l ?c ?H => apply (UniqueInterDiameterPoint l c H M); [try immEquiOriented | try immOnCircle]
	| |- InterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueInterDiameterPoint l c H M);  [try immEquiOriented | try immOnCircle]

	| |- ?M = SecondInterDiameterPoint ?l ?c ?H => apply (UniqueSecondInterDiameterPoint l c H M); [try immEquiOriented | try immOnCircle]
	| |- SecondInterDiameterPoint ?l ?c ?H = ?M => apply sym_eq; apply (UniqueSecondInterDiameterPoint l c H M);  [try immEquiOriented | try immOnCircle]

(* point reporte sur une droite *)
	| |- ?M = AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 => apply (UniqueAddSegmentPoint A B C D E H H0 M); [try immEquiOriented | try solveDistance]
	| |- AddSegmentPoint ?A ?B ?C ?D ?E ?H ?H0 = ?M => apply sym_eq; apply (UniqueAddSegmentPoint A B C D E H H0 M); [try immEquiOriented | try solveDistance]

	| |- ?M = MarkSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueMarkSegmentPoint A B C D H M); [try immClosedRay | try solveDistance]
	| |- MarkSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueMarkSegmentPoint A B C D H M); [try immClosedRay | try solveDistance]

	| |- ?M = OppSegmentPoint ?A ?B ?C ?D ?H => apply (UniqueOppSegmentPoint A B C D H M); [try immSegment | try solveDistance]
	| |- OppSegmentPoint ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueOppSegmentPoint A B C D H M); [try immSegment | try solveDistance]

(* symetrique d'un point *)
	| |- ?M = SymmetricPoint ?A ?B ?H => apply (UniqueSymmetricPoint A B H M); [try immBetween | try solveDistance]
	| |- SymmetricPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueSymmetricPoint A B H M); [try immBetween | try solveDistance]

(* milieu d'un segment *)
	| |- ?M = MidPoint ?A ?B ?H => apply (UniqueMidPoint A B H M); [try immCollinear | try solveDistance]
	| |- MidPoint ?A ?B ?H = ?M => apply sym_eq; apply (UniqueMidPoint A B H M); [try immCollinear | try solveDistance]

(* centre d'un parallelogramme *)
	| |- ?M = PCenter ?A ?B ?C ?D ?H => apply (UniquePCenter A B C D M H); first [right; split; immediate | left; split; immediate | idtac]
	| |- PCenter ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniquePCenter A B C D M H); first [right; split; immediate | left; split; immediate | idtac]

	| |- ?M = SPCenter ?A ?B ?C ?D ?H => apply (UniqueSPCenter A B C D M H); first [right; split; immediate | left; split; immediate | idtac]
	| |- SPCenter ?A ?B ?C ?D ?H = ?M => apply sym_eq; apply (UniqueSPCenter A B C D M H); first [right; split; immediate | left; split; immediate | idtac]

(* quatrieme sommet d'un parallelogramme *)
	| |- ?M = StrictPVertex4 ?A ?B ?C ?H => apply (UniqueStrictPVertex4 A B C M H); try immStrictParallelogramm
	| |- StrictPVertex4 ?A ?B ?C ?H = ?M => apply sym_eq; apply (UniqueStrictPVertex4 A B C M H); try immStrictParallelogramm

(* intersection de deux droites perpendiculaires *)
	| |- ?M = PerpendicularPoint ?d1 ?d2 ?Hp => apply (UniquePerpendicularPoint M d1 d2 Hp); try immOnLine
	| |- PerpendicularPoint ?d1 ?d2 ?Hp = ?M => apply sym_eq; apply (UniquePerpendicularPoint M d1 d2 Hp); try immOnLine
end.

Ltac stepEq X Y H  := match type of H with

(* si "H" est un point *)
	| Point => match goal with

(* definissant un angle supplementaire sur le cercle unite *)
			| |- X = Supplementary H _ => apply SupplementarySym; try immediate
			| |- Supplementary H _= Y  => apply sym_eq; apply SupplementarySym; try immediate

(* egal aux deux membres de l'egalite par definition de ce point *)
			| _ => apply trans_eq with (y:=H); unfold H; byDefEqPoint
		end

(* car le point "A" est sur le cercle "c" *)
	| OnCircle ?c ?A  => simplCircleHyp H; try solveDist

(* car les deux points sont la meme intersection de deux cercles *)
	| SecantCircles ?c1 ?c2 => apply (EqPointsIntersectionCircles c1 c2 H); try immediate

(* car les deux points sont la meme intersection de deux droites *)
	| SecantLines ?l1 ?l2 => apply (EqPointsInterLines l1 l2 H X Y); try immediate
	| ~EquiDirected ?A ?B ?C ?D => apply (EqPointsNotEquiDirectedInter A B C D X Y H); try immediate

(* car les deux points sont la meme intersection d'une droite et d'un cercle *)
	| Diameter ?l ?c => apply (EqPointsInterDiameter l c H); try immediate

(* car les deux points sont la meme intersection de deux droites *)
	| ~Collinear X ?B ?C  => apply (EqPointsNotCollinear X B C Y H); try immediate
	| ~Collinear Y ?B ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X H); try immediate
	| ~Collinear ?B X  ?C  => apply (EqPointsNotCollinear X B C Y); try immediate
	| ~Collinear ?B Y  ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate
	| ~Collinear ?B ?C X  => apply (EqPointsNotCollinear X B C Y); try immediate
	| ~Collinear ?B ?C Y  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate

	| Clockwise X ?B ?C  => apply (EqPointsNotCollinear X B C Y); try immediate
	| Clockwise Y ?B ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate
	| Clockwise ?B X  ?C  => apply (EqPointsNotCollinear X B C Y); try immediate
	| Clockwise ?B Y  ?C  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate
	| Clockwise ?B ?C X  => apply (EqPointsNotCollinear X B C Y); try immediate
	| Clockwise ?B ?C Y  => apply sym_eq; apply (EqPointsNotCollinear Y B C X); try immediate

(* car la distance separant les deux points est nulle *)
	| DistancePlus (Distance ?A ?B) (Distance X Y) = _ => apply (DistancePlusRightCancell A B X Y); rewrite H; try immediate
	| DistancePlus (Distance ?A ?B) (Distance Y X) = _ => apply sym_eq; apply (DistancePlusRightCancell A B Y X); rewrite H; try immediate
	| _ = DistancePlus (Distance ?A ?B) (Distance X Y) => apply (DistancePlusRightCancell A B X Y); rewrite <- H; try immediate
	| _ = DistancePlus (Distance ?A ?B) (Distance Y X) => apply sym_eq; apply (DistancePlusRightCancell A B Y X); rewrite <- H; try immediate

	| DistancePlus (Distance X Y) (Distance ?A ?B) = _ => apply (DistancePlusLeftCancell A B X Y); rewrite H; try immediate
	| DistancePlus (Distance Y X) (Distance ?A ?B) = _ => apply sym_eq; apply (DistancePlusLeftCancell A B Y X); rewrite H; try immediate
	| _ = DistancePlus  (Distance X Y) (Distance ?A ?B) => apply (DistancePlusLeftCancell A B X Y); rewrite <- H; try immediate
	| _ = DistancePlus (Distance Y X) (Distance ?A ?B) => apply sym_eq; apply (DistancePlusLeftCancell A B Y X); rewrite <- H; try immediate

(* car les deux points definissent le meme cote d'un angle *)
	| Angle ?C ?A ?B ?Hac ?Hab = Angle ?D ?A ?B ?Had ?Hab => eqToCongruent; apply (EqAngleUniquePointSide1 A B C D); try immediate
	| Angle ?B ?A ?C ?Hab ?Hac = Angle ?B ?A ?D ?Hab ?Had =>  eqToCongruent; apply (EqAngleUniquePointSide2 A B C D); try immediate

	| CongruentAngle ?C ?A ?B ?D ?A ?B =>  apply (EqAngleUniquePointSide1 A B C D H); try immediate
	| CongruentAngle ?B ?A ?C ?B ?A ?D  => apply (EqAngleUniquePointSide2 A B C D H); try immediate

(* car un des deux points definit un angle sur le cercle unite*)
	| IsAngle X => apply EqAngle; try immediate
	| IsAngle Y => apply EqAngle; try immediate

(* par trabnsitivite de l'egalite *)
	| X = ?Z => rewrite H; try solveEq
	| Y = ?Z => rewrite H; try solveEq
	| ?Z = X => rewrite <- H; try solveEq
	| ?Z = Y => rewrite <- H; try solveEq

	| ?Z = ?T => first 
			[let Hyp := fresh in (assert (Hyp : X=Z); [solveEq | rewrite Hyp; clear Hyp; rewrite H; try solveEq]) |
			let Hyp := fresh in (assert (Hyp : Y=Z); [solveEq | rewrite Hyp ; clear Hyp; rewrite H; try solveEq]) |
			let Hyp := fresh in (assert (Hyp : X=T); [solveEq | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq]) |
			let Hyp := fresh in (assert (Hyp : Y=T); [solveEq | rewrite Hyp ; clear Hyp; rewrite <- H; try solveEq])]
end.

Ltac stepDistinct A B H := match type of H with

(* en utilisant l'hypothese "H", il vient *)
	| A <> ?C => apply (DistinctOrDistinctABC A C B H); try solve [left; immediate | right; left; immediate | do 2 right; immediate]
	| ?C <> A => apply (DistinctOrDistinctABC A C B (sym_not_eq H));  try solve [left; immediate | right; left; immediate | do 2 right; immediate]
	| B <> ?C => apply sym_not_eq; apply (DistinctOrDistinctABC B C A H); try solve [left; immediate | right; left; immediate | do 2 right; immediate]
	| ?C <> B => apply sym_not_eq; apply (DistinctOrDistinctABC B C A (sym_not_eq H)); try solve [left; immediate | right; left; immediate | do 2 right; immediate]

	| ?C <> ?D => apply (DistinctOrDistinct C D A B H); try solve [left; immediate | right; immediate]

(* en utilisant la distance entre les deux points, il vient *)
	| Distance ?C ?D = Distance A B =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate | exact H]
	| Distance ?C ?D = Distance B A =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate | immediate]
	| Distance A B = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate | immediate]
	| Distance B A = Distance ?C ?D =>  apply (DistinctEqDistanceDistinct C D A B); [try immediate | immediate]

	| ?d = Distance A B =>  apply (DistanceEqDistanceDistinct A B d); [try immediate | immediate]
	| ?d = Distance B A =>  apply (DistanceEqDistanceDistinct A B d); [try immediate | immediate]
	| Distance A B = ?d =>  apply (DistanceEqDistanceDistinct A B d); [try immediate | immediate]
	| Distance B A = ?d =>  apply (DistanceEqDistanceDistinct A B d); [try immediate | immediate]

(* car un point est sur une demi-droite issue de l'autre point*)
	| OpenRay A ?C B => apply (OpenRayDistinct A C B); [try immediate | exact H]
	| OpenRay B ?C A => apply sym_not_eq; apply (OpenRayDistinct B C A); [try immediate | exact H]

	| EquiOriented ?C ?D A B => apply (EquiOrientedDistinct C D A B);  [try immediate | exact H]
	| EquiOriented ?C ?D B A =>  apply sym_not_eq; apply (EquiOrientedDistinct C D B A);  [try immediate | exact H]

(* car les points sont deux sommets d'un triangle oriente*)
	| Clockwise ?C ?D A => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate | try immediate]
	| Clockwise ?D A ?C => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate | try immediate]
	| Clockwise A ?C ?D => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate | try immediate]
	| Clockwise ?C ?D B => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate | try immediate]
	| Clockwise ?D B ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate | try immediate]
	| Clockwise B ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate | try immediate]

(* car l'un des points est colineaire a deux points distincts et pas l'autre*)
	| Collinear ?C ?D A => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate | try immediate]
	| Collinear ?D A ?C => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate | try immediate]
	| Collinear A ?C ?D => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate | try immediate]
	| Collinear ?C ?D B => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate | try immediate]
	| Collinear ?D B ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate | try immediate]
	| Collinear B ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate | try immediate]

(* car les orientations des deux points avec deux autres points sont diffŽrentes*)
	| ~Clockwise ?C ?D B => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate | try immediate]
	| ~Clockwise ?D B ?C => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate | try immediate]
	| ~Clockwise B ?C ?D => apply (FigureDistinct (fun M => Clockwise C D M) A B); [immediate | try immediate]
	| ~Clockwise ?C ?D A => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate | try immediate]
	| ~Clockwise ?D A ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate | try immediate]
	| ~Clockwise A ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Clockwise C D M) B A); [immediate | try immediate]

(* car l'un des points n'est pas colineaire a deux points distincts et pas l'autre*)
	| ~Collinear ?C ?D B => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate | try immediate]
	| ~Collinear ?D B ?C => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate | try immediate]
	| ~Collinear B ?C ?D => apply (FigureDistinct (fun M => Collinear C D M) A B); [immediate | try immediate]
	| ~Collinear ?C ?D A => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate | try immediate]
	| ~Collinear ?D A ?C => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate | try immediate]
	| ~Collinear A ?C ?D => apply sym_not_eq;  apply (FigureDistinct (fun M => Collinear C D M) B A); [immediate | try immediate]

(* par substitution *)
	| ?C = ?D => (rewrite H || rewrite <- H || apply (DistinctEqDistanceDistinct C D A B)); try immediate

(* car l'un des points appartient a la droite "H" *)
	| Line => match goal with
		| Ha : OnLine H A |- _ => apply (OnLineDistinct A B H Ha); try immediate
		| Hb : OnLine H B  |- _=> apply sym_not_eq;  apply (OnLineDistinct B A H Hb); try immediate
		| Hna : ~OnLine H A |- _ => apply sym_not_eq;  apply (OnLineDistinct B A H); [try immediate| apply Hna]
		| Hnb : ~OnLine H B |- _ => apply (OnLineDistinct A B H); [try immediate | apply Hnb]
		| _  => apply (OnLineDistinct A B H); try immediate
	end
end.

Ltac stepCollinear H := match type of H with

(* les points sont sur la droite "H" *)
	| Line => apply (OnLine3 H); try immediate

(* deux des points sont points de construction d'une droite *)
	| OnLine (Ruler _ _ _) _ =>  unfold OnLine in H; simpl in H; try immCollinear
	| Diameter (Ruler _ _ _) _ =>  unfold Diameter, OnLine in H; simpl in H; try immCollinear
	| OnLine ?l _ =>  unfold l, OnLine in H; simpl in H; try immCollinear
	| Diameter ?l _ =>  unfold l, Diameter, OnLine in H; simpl in H; try immCollinear
	| EquiOriented ?A ?B ?C ?D => stepEquiOrientedCollinear3 A B C D H

(*par transitivite *)
	| Collinear ?A ?B ?C => match goal with
		| Hab : A <> B |- Collinear A C ?D => apply (CollinearTrans A B C D Hab H); try immediate
		| Hba : B <> A |- Collinear A C ?D => apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate
		| Hab : A <> B |- Collinear C ?D A => apply CollinearBCA; apply (CollinearTrans A B C D Hab H); try immediate
		| Hba : B <> A |- Collinear C ?D A => apply CollinearBCA; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate
		| Hab : A <> B |- Collinear ?D A C => apply CollinearCAB ; apply (CollinearTrans A B C D Hab H); try immediate
		| Hba : B <> A |- Collinear ?D A C => apply CollinearCAB ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate
		| Hab : A <> B |- Collinear C A ?D => apply CollinearBAC ; apply (CollinearTrans A B C D Hab H); try immediate
		| Hba : B <> A |- Collinear C A ?D => apply CollinearBAC ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate
		| Hab : A <> B |- Collinear ?D C A => apply CollinearCBA; apply (CollinearTrans A B C D Hab H); try immediate
		| Hba : B <> A |- Collinear ?D C A => apply CollinearCBA; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate
		| Hab : A <> B |- Collinear A ?D C => apply CollinearACB ; apply (CollinearTrans A B C D Hab H); try immediate
		| Hba : B <> A |- Collinear A ?D C => apply CollinearACB ; apply (CollinearTrans A B C D (sym_not_eq Hba) H); try immediate
		| Hab : B <> A |- Collinear B C ?D => apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate
		| Hba : A <> B |- Collinear B C ?D => apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate
		| Hab : B <> A |- Collinear C ?D B => apply CollinearBCA; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate
		| Hba : A <> B |- Collinear C ?D B => apply CollinearBCA; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate
		| Hab : B <> A |- Collinear ?D B C => apply CollinearCAB ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate
		| Hba : A <> B |- Collinear ?D B C => apply CollinearCAB ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate
		| Hab : B <> A |- Collinear C B ?D => apply CollinearBAC ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate
		| Hba : A <> B |- Collinear C B ?D => apply CollinearBAC ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate
		| Hab : B <> A |- Collinear ?D C B => apply CollinearCBA; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate
		| Hba : A <> B |- Collinear ?D C B => apply CollinearCBA; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate
		| Hab : B <> A |- Collinear B ?D C => apply CollinearACB ; apply (CollinearTrans B A C D Hab (CollinearBAC A B C H)); try immediate
		| Hba : A <> B |- Collinear B ?D C => apply CollinearACB ; apply (CollinearTrans B A C D (sym_not_eq Hba) (CollinearBAC A B C H)); try immediate
		| Hab : C <> B |- Collinear C A ?D => apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate
		| Hba : B <> C |- Collinear C A ?D => apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate
		| Hab : C <> B |- Collinear A ?D C => apply CollinearBCA; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate
		| Hba : B <> C |- Collinear A ?D C => apply CollinearBCA; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate
		| Hab : C <> B |- Collinear ?D C A => apply CollinearCAB ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate
		| Hba : B <> C |- Collinear ?D C A => apply CollinearCAB ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate
		| Hab : C <> B |- Collinear A C ?D => apply CollinearBAC ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate
		| Hba : B <> C |- Collinear A C ?D => apply CollinearBAC ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate
		| Hab : C <> B |- Collinear ?D A C => apply CollinearCBA; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate
		| Hba : B <> C |- Collinear ?D A C => apply CollinearCBA; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate
		| Hab : C <> B |- Collinear C ?D A => apply CollinearACB ; apply (CollinearTrans C B A D Hab (CollinearCBA A B C H)); try immediate
		| Hba : B <> C |- Collinear C ?D A => apply CollinearACB ; apply (CollinearTrans C B A D (sym_not_eq Hba) (CollinearCBA A B C H)); try immediate
		| Hab : B <> C |- Collinear B A ?D => apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate
		| Hba : C <> B |- Collinear B A ?D => apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate
		| Hab : B <> C |- Collinear A ?D B => apply CollinearBCA; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate
		| Hba : C <> B |- Collinear A ?D B => apply CollinearBCA; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate
		| Hab : B <> C |- Collinear ?D B A => apply CollinearCAB ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate
		| Hba : C <> B |- Collinear ?D B A => apply CollinearCAB ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate
		| Hab : B <> C |- Collinear A B ?D => apply CollinearBAC ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate
		| Hba : C <> B |- Collinear A B ?D => apply CollinearBAC ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate
		| Hab : B <> C |- Collinear ?D A B => apply CollinearCBA; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate
		| Hba : C <> B |- Collinear ?D A B => apply CollinearCBA; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate
		| Hab : B <> C |- Collinear B ?D A => apply CollinearACB ; apply (CollinearTrans B C A D Hab (CollinearBCA A B C H)); try immediate
		| Hba : C <> B |- Collinear B ?D A => apply CollinearACB ; apply (CollinearTrans B C A D (sym_not_eq Hba) (CollinearBCA A B C H)); try immediate
		| Hab : A <> C |- Collinear A B ?D => apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate
		| Hba : C <> A |- Collinear A B ?D => apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate
		| Hab : A <> C |- Collinear B ?D A => apply CollinearBCA; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate
		| Hba : C <> A |- Collinear B ?D A => apply CollinearBCA; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate
		| Hab : A <> C |- Collinear ?D A B => apply CollinearCAB ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate
		| Hba : C <> A |- Collinear ?D A B => apply CollinearCAB ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate
		| Hab : A <> C |- Collinear B A ?D => apply CollinearBAC ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate
		| Hba : C <> A |- Collinear B A ?D => apply CollinearBAC ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate
		| Hab : A <> C |- Collinear ?D B A => apply CollinearCBA; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate
		| Hba : C <> A |- Collinear ?D B A => apply CollinearCBA; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate
		| Hab : A <> C |- Collinear A ?D B => apply CollinearACB ; apply (CollinearTrans A C B D Hab (CollinearACB A B C H)); try immediate
		| Hba : C <> A |- Collinear A ?D B => apply CollinearACB ; apply (CollinearTrans A C B D (sym_not_eq Hba) (CollinearACB A B C H)); try immediate
		| Hab : C <> A |- Collinear C B ?D => apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate
		| Hba : A <> C |- Collinear C B ?D => apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate
		| Hab : C <> A |- Collinear B ?D C => apply CollinearBCA; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate
		| Hba : A <> C |- Collinear B ?D C => apply CollinearBCA; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate
		| Hab : C <> A |- Collinear ?D C B => apply CollinearCAB ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate
		| Hba : A <> C |- Collinear ?D C B => apply CollinearCAB ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate
		| Hab : C <> A |- Collinear B C ?D => apply CollinearBAC ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate
		| Hba : A <> C |- Collinear B C ?D => apply CollinearBAC ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate
		| Hab : C <> A |- Collinear ?D B C => apply CollinearCBA; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate
		| Hba : A <> C |- Collinear ?D B C => apply CollinearCBA; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate
		| Hab : C <> A |- Collinear C ?D B => apply CollinearACB ; apply (CollinearTrans C A B D Hab (CollinearCAB A B C H)); try immediate
		| Hba : A <> C |- Collinear C ?D B => apply CollinearACB ; apply (CollinearTrans C A B D (sym_not_eq Hba) (CollinearCAB A B C H)); try immediate
		end

(* par egalite d'angles *)
	| CongruentAngle ?A ?B ?C ?D ?E ?F => match goal with
		| |- Collinear D E F => apply (CongruentAngleCollinear A B C D E F); try immediate
		| |- Collinear D F E => apply CollinearACB; apply (CongruentAngleCollinear A B C D E F); try immediate
		| |- Collinear E D F => apply CollinearBAC; apply (CongruentAngleCollinear A B C D E F); try immediate
		| |- Collinear E F D => apply CollinearBCA; apply (CongruentAngleCollinear A B C D E F); try immediate
		| |- Collinear F D E => apply CollinearCAB; apply (CongruentAngleCollinear A B C D E F); try immediate
		| |- Collinear F E D => apply CollinearCBA; apply (CongruentAngleCollinear A B C D E F); try immediate

		| |- Collinear A B C => apply (CongruentAngleCollinear D E F A B C); try immediate
		| |- Collinear A C B => apply CollinearACB; apply (CongruentAngleCollinear D E F A B C); try immediate
		| |- Collinear B A C => apply CollinearBAC; apply (CongruentAngleCollinear D E F A B C); try immediate
		| |- Collinear B C A => apply CollinearBCA; apply (CongruentAngleCollinear D E F A B C); try immediate
		| |- Collinear C A B => apply CollinearCAB; apply (CongruentAngleCollinear D E F A B C); try immediate
		| |- Collinear C B A => apply CollinearCBA; apply (CongruentAngleCollinear D E F A B C); try immediate
		end

(* par reecriture *)
	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate
end.

Ltac stepEquiOriented A B C D H := match type of H with

(* en utilisant les axiomes d'orientation *)
 	|  EquiOriented C D A B => apply (ChangeAll _ _ _ _ H); [try immDistinct | try ((left; immCollinear) || (right; immCollinear))]
 	|  EquiOriented D C B A => apply (ChangeSide _ _ _ _ H); try immDistinct
 	|  EquiOriented B A D C => apply (ChangeSense _ _ _ _ H); try immCollinear

 (* par transitivite *)
	|  EquiOriented A B ?E ?F => apply (EquiOrientedTrans A B E F C D H); try immEquiOriented
 	|  EquiOriented B A ?F ?E => apply (EquiOrientedTrans A B E F C D); [stepEquiOriented A B E F H | try immEquiOriented]
 	|  EquiOriented ?E ?F A B => apply (EquiOrientedTrans A B E F C D); [stepEquiOriented A B E F H  | try immEquiOriented]
 	|  EquiOriented ?F ?E B A => apply (EquiOrientedTrans A B E F C D); [stepEquiOriented A B E F H  | try immEquiOriented]

 	|  EquiOriented ?E ?F C D => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented | exact H]
	|  EquiOriented ?F ?E D C => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented | stepEquiOriented E F C D H]
 	|  EquiOriented C D ?E ?F => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented | stepEquiOriented E F C D H]
 	|  EquiOriented D C ?F ?E => apply (EquiOrientedTrans A B E F C D); [try immEquiOriented | stepEquiOriented E F C D H]

 (* par definition *)
	| OpenRay _ _ _ => unfold OpenRay in H; stepEquiOriented A B C D H
	| ClosedRay _ _ _ => unfold ClosedRay in H; stepEquiOriented A B C D H
	| Between ?E ?F ?G => let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in
					 (assert (Hyp1 := BetweenOpenRayAB E F G H); 
					 assert (Hyp2 := BetweenOpenRayAC E F G H); 
					 assert (Hyp3 := BetweenOpenRayCB E F G H));
					try immediate
	| Segment ?E ?F ?G => let Hyp1 := fresh in let Hyp2 := fresh in let Hyp3 := fresh in let Hyp4 := fresh in
					 (assert (Hyp1 := SegmentOpenRayAB E F G H); 
					 assert (Hyp2 := SegmentOpenRayAC E F G H); 
					 assert (Hyp3 := SegmentOpenRayAB F E G (SegmentSym _ _ _ H)); 
					 assert (Hyp4 := SegmentOpenRayAC F E G (SegmentSym _ _ _ H)));
					try immediate
	| ?E <> ?F -> EquiOriented _  _ _ _ => let Hyp1 := fresh in let Hyp2 := fresh in
				(assert (Hyp1 : E <> F); [try immediate  | assert (Hyp2 := H Hyp1);stepEquiOriented A B C D Hyp2])


 (*comme cote de parallelogramme *)
	| Parallelogramm ?X ?Y ?Z ?T => first [
		let Hyp := fresh in (assert (Hyp : StrictParallelogramm X Y Z T H); [immediate | try immediate]) |
		let Hyp := fresh in (assert (Hyp : Collinear X Y (PCenter X Y Z T H)); [immediate | try immediate]) ]


 (* par reecriture *)
	| ?C = ?D => (rewrite H || rewrite <- H); try immediate
end.

Ltac stepOpenRay A B C H := match type of H with

(* par definition*)
	| OpenRay A C B => apply OpenRaySym; [try immDistinct | exact H]
	| EquiOriented A C A B => apply OpenRaySym; [try immDistinct | apply H]
	| ClosedRay A B C => apply OpenRaySym; [try immDistinct | apply H]
	| OpenRay A B ?D => apply (OpenRayTrans A B D C) ; try immOpenRay
	| EquiOriented A B A ?D => apply (OpenRayTrans A B D C) ; try immOpenRay
	| ClosedRay A ?D B => apply (OpenRayTrans A B D C) ; try immOpenRay
	| OpenRay A ?D C => apply (OpenRayTrans A B D C) ; try immOpenRay
	| EquiOriented A ?D A C => apply (OpenRayTrans A B D C) ; try immOpenRay
	| ClosedRay A C ?D => apply (OpenRayTrans A B D C) ; try immOpenRay
	| EquiOriented ?D B A C => apply ClosedRayOpenRay; apply (EquiOrientedClosedRayClosedRay A C D B H); try immClosedRay

	| Segment A C B => apply SegmentOpenRayAC; exact H
	| Segment C A B => apply SegmentOpenRayAC; apply (SegmentSym _ _ _ H)
	| Segment A B C => apply SegmentOpenRayAB; try immediate
	| Segment B A C => apply SegmentOpenRayAB; try immediate

(* en utilisant l'egalite d'angles *)
	| Angle ?C ?A ?B ?Hac ?Hab = Angle ?D ?A ?B ?Had ?Hab => eqToCongruent; apply (EqAngleOpenRay1 A B C D); try immediate
	| Angle ?B ?A ?C ?Hab ?Hac = Angle ?B ?A ?D ?Hab ?Had => eqToCongruent; apply (EqAngleOpenRay2 A B C D); try immediate

	| CongruentAngle ?C ?A ?B ?D ?A ?B => apply (EqAngleOpenRay1 A B C D); try immediate
	| CongruentAngle ?B ?A ?C ?B ?A ?D => apply (EqAngleOpenRay2 A B C D); try immediate

(* cas particulier de l'angle nul "H = Uu" *)
	| Point => match H with
		| Uu => apply NullAngleOpenRay; try immediate
		end

(* par reecriture*)
	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate
end.

Ltac stepEquiOrientedClockwise H := match type of H with
	| EquiOriented ?A ?B ?C ?D => match goal with
			| |- Clockwise C D _ => apply H; try immClockwise
			| |- Clockwise _ C D => apply ClockwiseCAB; apply H; try immClockwise
			| |- Clockwise D _ C => apply ClockwiseBCA; apply H; try immClockwise

			| |- Clockwise D C _ => let Hyp := fresh in (assert (Hyp : EquiOriented B A D C); [stepEquiOriented B A D C H | apply Hyp; try immClockwise])
			| |- Clockwise _ D C => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented B A D C); [stepEquiOriented B A D C H | apply Hyp; try immClockwise])
			| |- Clockwise C _ D => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented B A D C); [stepEquiOriented B A D C H | apply Hyp; try immClockwise])

			| |- Clockwise A B _ => let Hyp := fresh in (assert (Hyp : EquiOriented C D A B); [stepEquiOriented C D A B H | apply Hyp; try immClockwise])
			| |- Clockwise _ A B => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented C D A B); [stepEquiOriented C D A B H | apply Hyp; try immClockwise])
			| |- Clockwise B _ A => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented C D A B); [stepEquiOriented C D A B H | apply Hyp; try immClockwise])

			| |- Clockwise B A _ => let Hyp := fresh in (assert (Hyp : EquiOriented D C B A); [stepEquiOriented D C B A H | apply Hyp; try immClockwise])
			| |- Clockwise _ B A => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented D C B A); [stepEquiOriented D C B A H | apply Hyp; try immClockwise])
			| |- Clockwise A _ B => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented D C B A); [stepEquiOriented D C B A H | apply Hyp; try immClockwise])
		end
end.

Ltac stepOpenRayClockwise H := match type of H with
	| EquiOriented ?A ?B ?A ?C => match goal with
			| |- Clockwise A C _ => apply H; try immClockwise
			| |- Clockwise _ A C => apply ClockwiseCAB; apply H; try immClockwise
			| |- Clockwise C _ A => apply ClockwiseBCA; apply H; try immClockwise

			| |- Clockwise C A _ => let Hyp := fresh in (assert (Hyp : EquiOriented B A C A); [immEquiOriented | apply Hyp; try immClockwise])
			| |- Clockwise _ C A => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented B A C A); [immEquiOriented | apply Hyp; try immClockwise])
			| |- Clockwise A _ C => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented B A C A); [immEquiOriented | apply Hyp; try immClockwise])

			| |- Clockwise A B _ => let Hyp := fresh in (assert (Hyp : EquiOriented A C A B); [immEquiOriented | apply Hyp; try immClockwise])
			| |- Clockwise _ A B => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented A C A B); [immEquiOriented | apply Hyp; try immClockwise])
			| |- Clockwise B _ A => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented A C A B); [immEquiOriented | apply Hyp; try immClockwise])

			| |- Clockwise B A _ => let Hyp := fresh in (assert (Hyp : EquiOriented C A B A); [immEquiOriented | apply Hyp; try immClockwise])
			| |- Clockwise _ B A => apply ClockwiseCAB; let Hyp := fresh in (assert (Hyp : EquiOriented C A B A); [immEquiOriented | apply Hyp; try immClockwise])
			| |- Clockwise A _ B => apply ClockwiseBCA; let Hyp := fresh in (assert (Hyp : EquiOriented C A B A); [immEquiOriented | apply Hyp; try immClockwise])
		end
end.

Ltac stepBetweenClockwise H := match type of H with
	| Between ?A ?B ?C => match goal with
			| |- Clockwise A C ?M => apply (BetweenClockwiseOrClockwiseAC A B C M H); try solve [left;  immediate | right; immediate]
			| |- Clockwise ?M A C => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAC A B C M H); try solve [left;  immediate | right; immediate]
			| |- Clockwise C ?M A => apply ClockwiseBCA; apply (BetweenClockwiseOrClockwiseAC A B C M H); try solve [left;  immediate | right; immediate]

			| |- Clockwise A B ?M => apply (BetweenClockwiseOrClockwiseAB A B C M H); try solve [left;  immediate | right; immediate]
			| |- Clockwise ?M A B => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAB A B C M H); try solve [left;  immediate | right; immediate]
			| |- Clockwise B ?M A => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseAB A B C M H); try solve [left;  immediate | right; immediate]

			| |- Clockwise B C ?M =>  apply (BetweenClockwiseOrClockwiseBC A B C M H); try solve [left;  immediate | right; immediate]
			| |- Clockwise ?M B C => apply ClockwiseCAB;  apply (BetweenClockwiseOrClockwiseBC A B C M H); try solve [left;  immediate | right; immediate]
			| |- Clockwise C ?M B => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseBC A B C M H); try solve [left;  immediate | right; immediate]
		end

	| Between ?C ?B ?A => match goal with
			| |- Clockwise A C ?M => apply (BetweenClockwiseOrClockwiseAC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
			| |- Clockwise ?M A C => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
			| |- Clockwise C ?M A => apply ClockwiseBCA; apply (BetweenClockwiseOrClockwiseAC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]

			| |- Clockwise A B ?M => apply (BetweenClockwiseOrClockwiseAB A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
			| |- Clockwise ?M A B => apply ClockwiseCAB; apply (BetweenClockwiseOrClockwiseAB A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
			| |- Clockwise B ?M A => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseAB A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]

			| |- Clockwise B C ?M =>  apply (BetweenClockwiseOrClockwiseBC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
			| |- Clockwise ?M B C => apply ClockwiseCAB;  apply (BetweenClockwiseOrClockwiseBC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
			| |- Clockwise C ?M B => apply ClockwiseBCA;  apply (BetweenClockwiseOrClockwiseBC A B C M (BetweenSym _ _ _ H)); try solve [left;  immediate | right; immediate]
		end
end.

Ltac stepClockwise A B C H := match type of H with

(* en utilisant les definitions *)
	| OpenRay _ _ _ => unfold OpenRay in H; stepOpenRayClockwise H
	| ClosedRay _ _ _ => unfold ClosedRay in H; stepOpenRayClockwise H
	| forall M : Point, Clockwise ?D ?E M -> Clockwise ?D ?F M => fold (EquiOriented D E D F) in H; stepOpenRayClockwise H
	| forall M : Point, Clockwise ?D ?E M -> Clockwise ?F ?G M => fold (EquiOriented D E F G) in H; stepEquiOrientedClockwise H
	| EquiOriented _ _ _ _ => stepEquiOrientedClockwise H
	| Between _ _ _  => stepBetweenClockwise H
	| Segment ?X ?Y ?Z => let Hyp := fresh in (assert (Hyp : Between X Z Y); 
				[apply (SegmentBetween X Z Y H); try immediate | stepBetweenClockwise Hyp])

(* en utilisant des points alignes *)
	| Clockwise A ?D ?E => apply (OpenRaysClockwise A D E B C H); try immediate
	| Clockwise ?E A ?D => apply (OpenRaysClockwise A D E B C (ClockwiseBCA _ _ _ H)); try immediate
	| Clockwise ?D ?E A => apply (OpenRaysClockwise A D E B C (ClockwiseCAB _ _ _ H)); try immediate
	| Clockwise B ?D ?E => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A H); try immediate
	| Clockwise ?E B ?D => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A (ClockwiseBCA _ _ _ H)); try immediate
	| Clockwise ?D ?E B => apply ClockwiseCAB; apply (OpenRaysClockwise B D E C A (ClockwiseCAB _ _ _ H)); try immediate
	| Clockwise C ?D ?E => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B H); try immediate
	| Clockwise ?E C ?D => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B (ClockwiseBCA _ _ _ H)); try immediate
	| Clockwise ?D ?E C => apply ClockwiseBCA; apply (OpenRaysClockwise C D E A B (ClockwiseCAB _ _ _ H)); try immediate

(* par reecriture *)
	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate

(* en utilisant la construction de la mediatrice *)
	| context [(MidLine A B ?H1)] => apply (EquiOrientedMidLineClockwiseAB A B C H1); try immediate
	| context [(MidPoint A B ?H1)] => apply (EquiOrientedMidLineClockwiseAB A B C H1); try immediate
	| context [(MidLine B C ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseAB B C A H1); try immediate
	| context [(MidPoint B C ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseAB B C A H1); try immediate
	| context [(MidLine  C A ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseAB C A B H1); try immediate
	| context [(MidPoint C A ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseAB C A B H1); try immediate

	| context [(MidLine A C ?H1)] => apply (EquiOrientedMidLineClockwiseBA A C B H1); try immediate
	| context [(MidPoint A C ?H1)] => apply (EquiOrientedMidLineClockwiseBA A C B H1); try immediate
	| context [(MidLine C B ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseBA C B A H1); try immediate
	| context [(MidPoint C B ?H1)] => apply ClockwiseBCA; apply (EquiOrientedMidLineClockwiseBA C B A H1); try immediate
	| context [(MidLine B A ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseBA B A C H1); try immediate
	| context [(MidPoint B A ?H1)] => apply ClockwiseCAB; apply (EquiOrientedMidLineClockwiseBA B A C H1); try immediate
end.

Ltac stepBetweenSupplement A B C D := first
	[assert (~Clockwise C B A); [immediate | apply (ClockwiseSupplementAnglesBetween B A C D); try immediate] |
	assert (~Clockwise D B C); [immediate | apply (ClockwiseSupplementAnglesBetween B A C D); try immediate] |
	assert (~Clockwise A B C); [immediate | apply (AntiClockwiseSupplementAnglesBetween B A C D);  try immediate] |
	assert (~Clockwise C B D); [immediate | apply (AntiClockwiseSupplementAnglesBetween B A C D);  try immediate]].

Ltac stepBetweenOpposed A B C D E :=  first
	[assert (~Clockwise C B A); [immediate | apply (OpposedAnglesAntiClockwiseBetween B C A E D); try immediate] |
	assert (~Clockwise E B D); [immediate | apply (OpposedAnglesAntiClockwiseBetween B C A E D); try immediate] |
	assert (~Clockwise A B C); [immediate | apply (OpposedAnglesClockwiseBetween B C A E D);  try immediate] |
	assert (~Clockwise D B E); [immediate | apply (OpposedAnglesClockwiseBetween B C A E D);  try immediate]].

Ltac stepBetween A B D H := match type of H with

(* par definition*)
	| Segment A D B => apply SegmentBetween; try immediate
	| Segment D A B => apply BetweenSym; apply SegmentBetween; try immediate

	| OpenRay B ?C D => apply (OpenRayBetween A B C D H); try immediate
	| ClosedRay B D ?C => apply (OpenRayBetween A B C D); try immediate
	| OpenRay B D ?C => apply (OpenRayBetween A B C D H); try immediate
	| ClosedRay B ?C D => apply (OpenRayBetween A B C D); try immediate
	| EquiOriented B ?C B D => apply (OpenRayBetween A B C D); try immediate
	| OpenRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate
	| ClosedRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate
	| OpenRay B A ?C => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate
	| ClosedRay B ?C A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate
	| EquiOriented B ?C B A => apply BetweenSym; apply (OpenRayBetween D B C A H); try immediate

	| Between A B ?C => apply (OpenRayBetween A B C D); try immediate
	| Between ?C B A => apply (OpenRayBetween A B C D); try immediate
	| Between D B ?C => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate
	| Between ?C B D => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate
	| Segment A ?C B => apply (OpenRayBetween A B C D); try immediate
	| Segment ?C A B => apply (OpenRayBetween A B C D); try immediate
	| Segment D ?C B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate
	| Segment ?C D B => apply BetweenSym; apply (OpenRayBetween D B C A); try immediate

	| Between ?E B ?F => apply (OpenRaysBetween B E F A D H); try immediate

(* en utilisant les angles *)
	| Supplement ?C B D A B ?C  => stepBetweenSupplement A B C D
	| Supplement A B ?C ?C B D   => stepBetweenSupplement A B C D
	| Supplement D B ?C A B ?C => stepBetweenSupplement A B C D
	| Supplement A B ?C D B ?C => stepBetweenSupplement A B C D
	| Supplement ?C B D ?C B A => stepBetweenSupplement A B C D
	| Supplement ?C B A ?C B D  => stepBetweenSupplement A B C D
	| Supplement D B ?C ?C B A   => stepBetweenSupplement A B C D
	| Supplement ?C B A  D B ?C  => stepBetweenSupplement A B C D

	| CongruentAngle ?C B A  D B ?E  => stepBetweenOpposed A B C D E
	| CongruentAngle A B ?C D B ?E  => stepBetweenOpposed A B C D E
	| CongruentAngle ?C B A ?E B D => stepBetweenOpposed A B C D E
	| CongruentAngle A B ?C ?E B D  => stepBetweenOpposed A B C D E
	| CongruentAngle D B ?E  ?C B A  => stepBetweenOpposed A B C D E
	| CongruentAngle D B ?E A B ?C  => stepBetweenOpposed A B C D E
	| CongruentAngle ?E B D ?C B A => stepBetweenOpposed A B C D E
	| CongruentAngle ?E B D A B ?C  => stepBetweenOpposed A B C D E

(* cas particulier de l'angle nul "H = uU" *)
	| Point => match H with
		| uU => apply ElongatedAngleBetween
		end

(* par reecriture*)
	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate
end.

Ltac stepSegment A B C H := match type of H with

(* par transitivite *)
	| EquiOriented C B A ?D => apply (EquiOrientedClosedRaySegment A D C B H); try immediate
	| ClosedRay A ?D C => apply (EquiOrientedClosedRaySegment A D C B); [try immediate | exact H]

(* par reecriture*)
	| ?C = ?D => (rewrite H || rewrite <- H); try immediate

(* par definition*)
	| _ => apply EquiOrientedSegment; stepEquiOriented A C C B H
end.

Ltac stepTriangleSpec A B C D E F H  := match type of H with

(* par reecriture*)
	| ?X = ?Y => (rewrite H || rewrite <- H); try immediate

(* par identification avec un triangle *)
	| TriangleSpec ?AA ?BB ?CC ?DD ?EE ?FF => apply (TriangleSpecEq AA BB CC DD EE FF A B C D E F H); try solveDistance
end.

Ltac stepOnLine d M H := match type of H with

(* "H" est la droite *)
	| Line => unfold H; match goal with
		| |- OnLine (MidLine _ _ _) _ => apply EqDistanceOnMidLine; try solveDist
		| |- OnLine (Ruler _ _ _) _ => simplGoal; try immCollinear
	end

(* par egalite de droites *)
	| EqLine ?d1 d => apply (EqLineOnLine d1 d M H); try immediate
	| EqLine d ?d2 => apply (EqLineOnLine d2 d M (EqLineSym d d2 H)); try immediate
	| OnLine ?d1 M => apply (EqLineOnLine d1 d M); [try immediate | apply H]

(* par collinearite *)
	| Collinear ?A ?B M => apply (OnLineTwoPoints A B M d); try immediate
	| Collinear ?A M ?B => apply (OnLineTwoPoints A B M d); try immediate
	| Collinear M ?A ?B => apply (OnLineTwoPoints A B M d); try immediate
end.

Ltac stepTStrict t H := match type of H with

(* par egalite avec un triangle non degenere *)
	| TCongruent ?t1 t => apply (TCongruentTStrict t1 t H); try immTStrict
	| TCongruent t ?t1 => apply (TCongruentTStrict t1 t (TCongruentSym t t1 H)); try immTStrict

	| TStrict ?t1 => apply (TCongruentTStrict t1 t); try immediate
	| Clockwise ?A ?B ?C => apply (TCongruentTStrict (Tr A B C) t); try immediate
end.

Ltac stepTCongruent H := match goal  with
	| |- TCongruent (Tr ?A ?B ?C) (Tr ?D ?E ?F) => match type of H with

(* par transitivite *)
		| TCongruent (Tr A B C) (Tr ?D' ?E' ?F') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F) H)
		| TCongruent (Tr B C A) (Tr  ?E' ?F' ?D') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr C A B) (Tr  ?F' ?D'  ?E') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr B A C) (Tr ?E' ?D' ?F') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr A C B) (Tr  ?D' ?F' ?E') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr C B A) (Tr  ?F' ?E'  ?D') => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr ?D' ?E' ?F') (Tr A B C) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr  ?E' ?F' ?D') (Tr B C A) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr  ?F' ?D'  ?E') (Tr C A B) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr ?E' ?D' ?F') (Tr B A C) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr  ?D' ?F' ?E') (Tr A C B) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate
		| TCongruent (Tr  ?F' ?E'  ?D') (Tr C B A) => apply (TCongruentTrans (Tr A B C) (Tr D' E' F')  (Tr D E F)); try immediate

		| TCongruent (Tr ?A' ?B' ?C') (Tr D E F) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr ?B' ?C' ?A') (Tr  E F D) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr ?C' ?A' ?B') (Tr  F D  E) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr ?B' ?A' ?C') (Tr E D F) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr ?A' ?C' ?B') (Tr  D F E) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr ?C' ?B' ?A') (Tr  F E  D) => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr D E F) (Tr ?A' ?B' ?C') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr  E F D) (Tr ?B' ?C' ?A') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr  F D  E) (Tr ?C' ?A' ?B') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr E D F) (Tr ?B' ?A' ?C') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr  D F E) (Tr ?A' ?C' ?B') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
		| TCongruent (Tr  F E  D) (Tr ?C' ?B' ?A') => apply (TCongruentTrans (Tr A B C) (Tr A' B' C')  (Tr D E F)); try immediate
	end
end.

Ltac stepStrictParallelogramm A B C D H := match type of H with

(* par definition d'un parallelogramme strict a partir d'un parallelogramme *)
	|  Parallelogramm A B C D => apply (SPDef H);  try immediate

(* par egalite de cote *)
	| Distance _ _ = Distance _ _ => apply EquiDistantStrictParallelogramm; try immediate

(* par orientation *)
	| Clockwise _ _ _ => apply EquiDistantStrictParallelogramm; try immediate

(* par egalite d'angles opposes *)
	| CongruentAngle A B D B D C => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle D B A B D C => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle A B D C D B => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle D B A C D B => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle B D C A B D => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle B D C D B A => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle C D B A B D => apply CongruentAnglesParallelogramm;  try immediate
	| CongruentAngle C D B D B A => apply CongruentAnglesParallelogramm;  try immediate

(* car ayant deux angles adjascents supplementaires *)
	| Supplement A B C B C D => apply SupplementParallelogramm;  try immediate
	| Supplement C B A B C D => apply SupplementParallelogramm;  try immediate
	| Supplement A B C D C B => apply SupplementParallelogramm;  try immediate
	| Supplement C B A D C B => apply SupplementParallelogramm;  try immediate
	| Supplement B C D A B C => apply SupplementParallelogramm;  try immediate
	| Supplement B C D C B A => apply SupplementParallelogramm;  try immediate
	| Supplement D C B A B C => apply SupplementParallelogramm;  try immediate
	| Supplement D C B C B A => apply SupplementParallelogramm;  try immediate

end.

Ltac stepParallelogramm A B C D H := match type of H with

(* par definition du point "H" *)
	| Point => unfold H; try immParallelogramm

(* par definition de parallelogramme *)
	| A <> C => match goal with
			| Hbd : B <> D |- _ => apply (Pllgm A B C D H Hbd); try immediate
			| Hdb : D <> B |- _  => apply (Pllgm A B C D H (sym_not_eq Hdb)); try immediate
			|  _ => let Hbd := fresh in (assert (Hbd : B <> D);
						[try immediate | apply (Pllgm A B C D H Hbd); try immediate])
		end
	| C <> A => match goal with
			| Hbd : B <> D |- _  => apply (Pllgm A B C D (sym_not_eq H) Hbd); try immediate
			| Hdb : D <> B |- _  => apply (Pllgm A B C D (sym_not_eq H) (sym_not_eq Hdb)); try immediate 
			| _ => let Hbd := fresh in (assert (Hbd : B <> D);
						[try immediate | apply (Pllgm A B C D (sym_not_eq H) Hbd); try immediate])
		end
	| B <> D => match goal with
			| Hac : A <> C |- _  => apply (Pllgm A B C D Hac H); try immediate
			| Hca : C <> A |- _  => apply (Pllgm A B C D (sym_not_eq Hca)); try immediate
			| _ => let Hac := fresh in (assert (Hac : A <> C);
						[try immediate | apply (Pllgm A B C D H Hac); try immediate])
		end
	| D <> B => match goal with
			| Hac : A <> C |- _  => apply (Pllgm A B C D Hac (sym_not_eq H)); try immediate
			| Hca : C <> A |- _  => apply (Pllgm A B C D (sym_not_eq Hca) (sym_not_eq H)); try immediate
			| _ => let Hac := fresh in (assert (Hac : A <> C);
						[try immediate | apply (Pllgm A B C D Hac (sym_not_eq H)); try immediate])
		end

(* par egalite de cotes *)
	| Distance _ _ = Distance _ _ => first [
		 assert (Clockwise A B C); [immediate | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm A B C D H | immediate]] |
		 assert (Clockwise B C D); [immediate | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm A B C D H | immediate]] |
		 assert (Clockwise C D A); [immediate | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm A B C D H | immediate]] |
		 assert (Clockwise D A B); [immediate | assert (StrictParallelogramm A B C D); 			[stepStrictParallelogramm A B C D H | immediate]] |

		 assert (Clockwise A C B); [immediate | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm A D C B H | immediate]] |
		 assert (Clockwise B D C); [immediate | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm A D C B H | immediate]] |
		 assert (Clockwise C A D); [immediate | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm A D C B H | immediate]] |
		 assert (Clockwise D B A); [immediate | assert (StrictParallelogramm A D C B); 			[stepStrictParallelogramm A D C B H | immediate]] ]

end.

Ltac stepEqLine d1 d2 H := match type of H with 

(* par transitivite avec la droite "H" *)
	| Line => apply (EqLineTrans d1 H d2); try immediate

(* par transitivite avec la droite "H" *)
	| EqLine d1 ?d3  => apply (EqLineTrans d1 d3 d2 H); try immediate
	| EqLine ?d3 d1  => apply (EqLineTrans d1 d3 d2 (EqLineSym d3 d1 H)); try immediate
	| EqLine d2 ?d3  => apply (EqLineTrans d1 d3 d2); [try immediate | apply (EqLineSym d2 d3 H)]
	| EqLine ?d3 d2  => apply (EqLineTrans d1 d3 d2); [try immediate | apply H]

(* car ayant deux points distincts communs *)	
	| ?A <> ?B => apply (EqLineTwoPoints A B d1 d2); try immediate

(* car ayant une paire "H" de points distincts communs *)	
	| (Point*Point)%type => match H with
		| (?A, ?B) => apply (EqLineTwoPoints A B d1 d2); try immediate
	end

(* car etant deux droites paralleles ayant un point commun *)	
	| ParallelLines d1 d2  => match goal with
		| Hm : OnLine d1 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate
		| Hm : OnLine d2 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate
	end

	| ParallelLines d2 d1  => match goal with
		| Hm : OnLine d1 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate
		| Hm : OnLine d2 ?M |- _ => apply (ParallelEqLine M d1 d2); immediate
	end

	| (Point*Line)%type => match H with
		| (?A, ?d0) => match goal with 

(* "H" etant un couple forme d'un point commun aux deux droites et d'une droite parallele aux deux droites *)
			| Hp : ParallelLines d0 d1 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate
			| Hp :  ParallelLines d1 d0 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate
			| Hp : ParallelLines d0 d2 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate
			| Hp : ParallelLines d2 d0 |- _ => apply (UniqueParallel d0 d1 d2 A); try immediate

(* "H" etant un couple forme d'un point commun aux deux droites et d'une droite perepndiculaire aux deux droites *)
			| Hp : Perpendicular d0 d1 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate
			| Hp : Perpendicular d1 d0 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate
			| Hp : Perpendicular d0 d2 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate
			| Hp : Perpendicular d2 d0 |- _ => apply (UniquePerpendicular d1 d2 d0 A); try immediate

		end
	end
end.

Ltac stepParallelLines d1 d2 H := match type of H with 

(* par transitivite avec la droite "H" *)
	| Line => apply (ParallelTrans d1 H d2); try immediate

(* par reecriture*)
	| EqLine d1 ?d3  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1); [try immediate | apply (EqLineSym d1 d3 H)]
	| EqLine ?d3 d1  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1); [try immediate | apply H]
	| EqLine d2 ?d3  => apply (ParallelEqParallelLine d1 d3 d2); [try immediate | apply (EqLineSym d2 d3 H)]
	| EqLine ?d3 d2  => apply (ParallelEqParallelLine d1 d3 d2); [try immediate | apply H]
	
	| ParallelLines d1 ?d3  => apply (ParallelEqParallelLine d1 d3 d2 H); try immediate
	| ParallelLines ?d3 d1  => apply (ParallelEqParallelLine d1 d3 d2 (ParallelLinesSym d3 d1 H)); try immediate
	| ParallelLines d2 ?d3  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1 H); try immediate
	| ParallelLines ?d3 d2  => apply ParallelLinesSym; apply (ParallelEqParallelLine d2 d3 d1 (ParallelLinesSym d3 d2 H)); try immediate
	
	| ParallelLines ?d3 ?d4  => apply (EqEqParallelLine d3 d4 d1 d2); try immediate
	

(* car etant deux droites perpendiculaires a une meme troisieme *)
	| Perpendicular d1 ?d3  => apply (PerpendicularPerpendicularParallel d1 d3 d2 H); try immediate
	| Perpendicular ?d3 d1  => apply (PerpendicularPerpendicularParallel d1 d3 d2 (PerpendicularSym d3 d1 H)); try immediate
	| Perpendicular d2 ?d3  => apply ParallelLinesSym; apply (PerpendicularPerpendicularParallel d2 d3 d1 H); try immediate
	| Perpendicular ?d3 d2  => apply ParallelLinesSym; apply (PerpendicularPerpendicularParallel d2 d3 d1 (PerpendicularSym d3 d2 H)); try immediate
end.

Ltac stepSecantLines d1 d2 H := match type of H with 

(* car deux droites ayant un point commun et un pont appartenant a l'une et non a l'autre sont secantes, "H" est ce couple de points *)
	| (Point*Point)%type => match H with 
		|  (?A, ?B) => apply (TwoPointsSecantLine d1 d2 A B); try immediate
		end

(* car une droite passant par deux points de part et d'autre d'un seconde droite est secante a celle-ci, "H" etant un couple de couple de points *)
	| ((Point*Point)*(Point*Point))%type => match H with
		|  ((?A, ?B), (?C, ?D)) => apply (FourPointsSecantLines d1 d2 A B C D); try immediate
		end

	| (Line*Line)%type => match H with
		| (?d3,?d4) => match goal with

(* car deux droites respectivement paralleles a deux droites secantes sont secantes, "H" etant un couple de droites *)
			| Hp : ParallelLines d1 d3 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d1 d4 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d3 d1 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d4 d1 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d2 d3 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d2 d4 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d3 d2 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate
			| Hp : ParallelLines d4 d2 |- _ => apply (SecantParallelSecant d3 d4 d1 d2); try immediate

(* car deux droites respectivement perpendiculaires a deux droites secantes sont secantes, "H" etant un couple de droites *)
			| Hp : Perpendicular d1 d3 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d1 d4 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d3 d1 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d4 d1 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d2 d3 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d2 d4 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d3 d2 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			| Hp : Perpendicular d4 d2 |- _ => apply (SecantPerpendicularSecant d3 d4 d1 d2); try immediate
			end
		end

(* par reecriture *)
	| EqLine ?d3 d1  => apply (EqSecantSecantLines d3 d1 d2 H); try immediate
	| EqLine d1 ?d3  => apply (EqSecantSecantLines d3 d1 d2 (EqLineSym d1 d3 H)); try immediate
	| EqLine ?d3 d2  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1 H); try immediate
	| EqLine d2 ?d3  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1  (EqLineSym d2 d3 H)); try immediate

	| SecantLines ?d3 d2  => apply (EqSecantSecantLines d3 d1 d2); [try immediate | apply H]
	| SecantLines d2 ?d3  =>  apply (EqSecantSecantLines d3 d1 d2); [try immediate | apply (SecantLinesSym d2 d3 H)]
	| SecantLines ?d3 d1  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1); [try immediate | apply H]
	| SecantLines d1 ?d3  => apply SecantLinesSym; apply (EqSecantSecantLines d3 d2 d1); [try immediate | apply (SecantLinesSym d1 d3 H)]

	| SecantLines ?d3 ?d4  => apply (EqEqSecantSecantLines d3 d1 d4 d2); try immediate

(* car si deux droites sont paralleles, toute secante a l'une est secante a l'autre *)
	| ParallelLines ?d0 d1  => apply (ParallelSecant d0 d1 d2 H); try immediate
	| ParallelLines d1 ?d0  => apply (ParallelSecant d0 d1 d2); try immediate
	| ParallelLines ?d0 d2  => apply ParallelLinesSym; apply (ParallelSecant d0 d2 d1 H); try immediate
	| ParallelLines d2 ?d0  => apply ParallelLinesSym; apply (ParallelSecant d0 d2 d1); try immediate
	
end.

Ltac stepPerpendicular d1 d2 H := match H with 

(* car deux droites formant un angle droit sont perpendiculaires, "H" est un triplet de points *)
	|  (?A, (?B, ?C)) => apply (PerpRightAngle d1 d2 A B C); try immediate

	| _ => match type of H with 

(* par reecriture *)
		| EqLine ?d3 d1  => apply (EqEqPerpendicular d3 d1 d2 d2); try immediate
		| EqLine d1 ?d3  => apply (EqEqPerpendicular d3 d1 d2 d2); try immediate
		| EqLine ?d3 d2  =>  apply (EqEqPerpendicular d1 d1 d3 d2); try immediate
		| EqLine d2 ?d3  => apply (EqEqPerpendicular d1 d1 d3 d2); try immediate
	
		| Perpendicular ?d3 d2  => apply (EqEqPerpendicular d3 d1 d2 d2);  try immediate
		| Perpendicular d2 ?d3  =>  apply (EqEqPerpendicular d3 d1 d2 d2);  try immediate
		| Perpendicular ?d3 d1  => apply (EqEqPerpendicular d1 d1 d3 d2);  try immediate
		| Perpendicular d1 ?d3  => apply (EqEqPerpendicular d1 d1 d3 d2); try immediate
	
		| Perpendicular ?d3 ?d4  => apply (EqEqPerpendicular d3 d1 d4 d2); try immediate

(* car si deux droites sont paralleles, toute perpendiculaire a l'une est perpendiculaire a l'autre *)
		| ParallelLines ?d0 d2  => apply (PerpendicularParallelPerpendicular d0 d1 d2); try immediate
		| ParallelLines d2 ?d0  => apply (PerpendicularParallelPerpendicular d0 d1 d2); try immediate
		| ParallelLines ?d0 d1  => apply ParallelLinesSym; apply (PerpendicularParallelPerpendicular d0 d2 d1); try immediate
		| ParallelLines d1 ?d0  => apply ParallelLinesSym; apply (PerpendicularParallelPerpendicular d0 d2 d1); try immediate
	end
end.

Ltac step H := match goal with

	| |- ?A /\ ?B => split; step H
	| |- ?A \/ ?B => (left; step H)  || (right; step H)

(* en utilisant l'hypothese "H", il vient *)
	| |- DistancePlus _ _  = _ => stepEqDistance H
	| |- _ = DistancePlus _ _  => stepEqDistance H
	| |- DistanceTimes _ _ _  = _ => stepEqDistance H
	| |- _ = DistanceTimes _ _ _  => stepEqDistance H
	| |- Distance _ _ = _ => stepEqDistance H
	| |- _ = Distance _ _ => stepEqDistance H

	| |- DistanceLe _ _  => stepDistanceLe H
	| |- DistanceLt _ _  => stepDistanceLt H

	| |-  Supplement ?A ?B ?C ?D ?E ?F => stepSupplement A B C D E F H
	| |-  OpposedAngles ?A ?B ?C ?D ?E => stepOpposed A B C D E H

	| |-  _ = Angle _ _ _ _ _ => eqToCongruent; try immediate
	| |-  Angle _ _ _ _ _ = _ => eqToCongruent; try immediate

	| |- CongruentAngle ?A ?B ?C ?D ?E ?F => stepCongruentAngle A B C D E F H
	| |- NullAngle ?A ?B ?C => stepNullAngle A B C H
	| |- ElongatedAngle ?A ?B ?C => stepElongatedAngle A B C H
	| |- RightAngle ?A ?B ?C => stepRightAngle A B C H

(* l'egalite se deduit de la definition du point "H" *)
	| |- _ = H => try unfold H; byDefEqPoint
	| |- H = _ => apply sym_eq; try unfold H; byDefEqPoint

(* en utilisant l'hypothese "H", il vient *)
	| |- ?A = ?B => stepEq A B H
	| |- ?A <> ?B => stepDistinct A B H
	| |- ?A = ?B -> False => fold (A <> B); stepDistinct A B H

	| |- Collinear _ _ _  => stepCollinear H
	| |- EquiOriented ?A ?B ?C ?D => stepEquiOriented A B C D H
	| |- OpenRay ?A ?B ?C => stepOpenRay A B C H
	| |- ClosedRay ?A ?B ?C => apply OpenRayClosedRay; stepOpenRay A C B H
	| |- Clockwise ?A ?B ?C => stepClockwise A B C H
	| |- Between ?A ?B ?D => stepBetween A B D H
	| |- Segment ?A ?B ?C  => stepSegment A B C H
	| |- TriangleSpec ?A ?B ?C ?D ?E ?F => stepTriangleSpec A B C D E F H

	| |- OnLine ?d ?M=> stepOnLine d M H
	| |- Diameter ?d ?c => unfold Diameter; simplCircle; step H

	| |- TStrict ?t => stepTStrict t H

	| |- TCongruent _ _ => stepTCongruent H

(* en utilisant l'hypothese "H" ou la definition du point "H", il vient *)
	| |- Parallelogramm ?A ?B ?C ?D => stepParallelogramm A B C D H
	| |- StrictParallelogramm ?A ?B ?C ?D => stepStrictParallelogramm A B C D H

(* selon les cas, "H" peut etre une droite, un couple de points, un couple forme d'un point et d'une droite ou une hypothese *)
	| |- EqLine ?d1 ?d2 => stepEqLine d1 d2 H

(* selon les cas, "H" peut etre une droite ou une hypothese *)
	| |- ParallelLines ?d1 ?d2 => stepParallelLines d1 d2 H

(* selon les cas, "H" peut etre un couple de points, un quadruplet de points, un couple de droites ou une hypothese *)
	| |- SecantLines ?d1 ?d2 => stepSecantLines d1 d2 H

(* selon les cas, "H" peut etre trois points ou une hypothese *)
	| |- Perpendicular ?d1 ?d2 => stepPerpendicular d1 d2 H

(* si "H" est une implication du but *)
	| _ => apply H; try immediate

end.
