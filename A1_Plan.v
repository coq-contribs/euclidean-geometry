Section PLANE.

(* On postule l'existence d'un ensemble de points. *)

Parameter Point : Set.

Axiom Oo Uu : Point.

Axiom DistinctOoUu : Oo <> Uu.

(* Les figures sont les sous ensembles de points dŽfinis par une propriŽtŽ. *)

Definition Figure := Point -> Prop.

(* Le singleton. *)

Definition Unicity := 
	fun (M: Point) (f : Figure) => forall N : Point, f N -> M = N.

End PLANE.
