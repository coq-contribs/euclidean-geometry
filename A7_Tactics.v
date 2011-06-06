Ltac contrapose0 H := let Hyp := fresh in 
	(intro Hyp; apply H; generalize Hyp; clear Hyp H);
	intro H. 

Ltac visibleConj0 := match goal with 
	| |- ?A /\ ?B => split 
end.

(* Ces tactiques deplient les definitions usuelles. *)

Ltac simplGoal0 := 
	unfold Segment, Between, Collinear, ClosedRay, OpenRay, EquiDirected, EquiOriented, HalfPlane; intros.

Ltac canonize1 := 
	unfold Segment, Between, Collinear, ClosedRay, OpenRay, EquiDirected, EquiOriented, HalfPlane in *; intuition.

Ltac simplLineHyp0 H  :=
	unfold SecantLines, ParallelLines in H; simpl OnLine in H; simpl LineH in H; simpl LineB in H; simpl LineA in H.

Ltac simplLine1  :=
	unfold SecantLines, ParallelLines in *; simpl OnLine in *;simpl LineH in *; simpl LineB in *; simpl LineA in *.

Ltac simplCircle1 := repeat match goal with
	| H: context [(Diameter _ _)] |- _ => unfold Diameter, OnLine in H
	| |- context [(Diameter _ _)]  => 	unfold Diameter, OnLine 
	| H: context [(SecantCircles1 _ _)] |- _ => unfold SecantCircles1 in H; decompose [and] H; clear H
	| |- context [(SecantCircles1 _ _)]  => unfold SecantCircles1
	| H: context [(TriangleSpec1 _ _ _ _ _ _)] |- _ => unfold TriangleSpec1 in H; decompose [and] H; clear H
	| |- context [(TriangleSpec1 _ _ _ _ _ _)] => unfold TriangleSpec1
end;
	simpl RadiusB in *; simpl RadiusA in *; simpl Center in *; repeat visibleConj0.

(* La tactique suivante cree la droite AB passant par A et B, si la preuve que A <> B n'est pas immediate, elle est demandee. *)

Ltac setLine0 A B lineAB := match goal with
	| H : A <> B |- _ => pose (lineAB := Ruler A B H)
	| H : B <> A |- _ => pose (lineAB := Ruler A B (sym_not_eq H))
	| H : A = B -> False |- _ => pose (lineAB := Ruler A B H)
	| H : B = A -> False |- _ => pose (lineAB := Ruler A B (sym_not_eq H))
	| _ => let Hyp := fresh in (assert (Hyp : A<> B) ; [idtac | pose (lineAB := Ruler A B Hyp)])
end.

(* La tactique suivante cree le cercle de centre C et de rayon AB. *)

Ltac setCircle0 C A B c := pose (c := Compass C A B).

(* Ces tactiques construisent les points d'intersection respectifs de deux droites, de deux cercles et d'une droite diametre d'un cercle. *)

Ltac setInterLines l1 l2 J :=
	let H1 := fresh "Hol" in let H2 := fresh "Hol" in let H3 := fresh "Hun" in
	(destruct (PointDef  (fun M : Point => OnLine l1 M /\ OnLine l2 M)) as (J, ((H1, H2), H3));	[apply (InterLines l1 l2); simpl; trivial | simpl in H1, H2, H3]).
	
Ltac setInterCircles1 c1 c2 J :=
	let H1 := fresh "Hoc" in let H2 := fresh "Hoc" in let H3 := fresh "Hck" in  let H4 := fresh "Hun" in
	(destruct (PointDef  
		(fun M : Point => OnCircle1 c1 M /\ OnCircle1 c2 M /\ ~Clockwise (Center c2) M (Center c1)))
		as (J, ((H1, (H2, H3)), H4));	
	[apply (InterCircles c1 c2); simpl; trivial | simpl in H1, H2, H3, H4]).
	
Ltac setInterDiameter1 l c J :=
	let H1 := fresh "Hoc" in let H2 := fresh "Heo" in let H3 := fresh "Hun" in
	(destruct (PointDef   
		(fun M : Point => OnCircle1 c M /\ EquiOriented  (Center c) M  (LineA l) (LineB l)))
		as (J, ((H1, H2), H3));	
	[apply (InterDiameter l c); simpl; trivial | simpl in H1, H2, H3]).
