Section INTERSECTION.

(* Une figure est une intersection dans les trois cas suivants : *)
(* - c'est l'ensemble des points communs a deux droites secantes; *)
(* - c'est l'ensemble des points communs a deux cercles secants non situes a gauche de la droite des centres; *)
(* - c'est l'ensemble des points commun a un cercle et un diametre situe par rapport au centre dans la meme direction que les points de construction. *)

Inductive Intersection : Figure -> Set :=
	| InterLines : forall l1 l2 : Line,  
		SecantLines l1 l2 -> 
		Intersection (fun M : Point => OnLine l1 M /\ OnLine l2 M)
	| InterCircles : forall c1 c2 : Circle,  
		SecantCircles1 c1 c2 -> 
		Intersection (fun M : Point => OnCircle1 c1 M /\ OnCircle1 c2 M /\ ~Clockwise (Center c2)  M (Center c1))
	| InterDiameter : forall (l : Line) (c : Circle),  
		Diameter l c -> 
		Intersection (fun M : Point => 
					OnCircle1 c M /\ EquiOriented (Center c) M (LineA l) (LineB l)).

(* Cet axiome affirme qu'a chaque intersection correspond la construction d'un unique point appartenant a l'intersection. *)

Axiom PointDef : forall f : Figure, forall If : Intersection f, {M : Point | f M /\ Unicity M f}.

End INTERSECTION.
