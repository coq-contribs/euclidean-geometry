Section EQUIDISTANT.

(* L'equidistance est une relation sur quatre points du plan definie axiomatiquement. *)

Parameter EquiDistant : Point -> Point -> Point -> Point -> Prop.

(* C'est une relation d'equivalence sur les bipoints. *)

Axiom EquiDistantRefl : forall A B : Point, EquiDistant A B A B.

Axiom EquiDistantRec : forall A B C D E F : Point,
	EquiDistant A B C D -> EquiDistant A B E F -> EquiDistant C D E F.

(* Il n'y a qu'une distance nulle. *)

Axiom EquiDistantAABB : forall A B : Point, EquiDistant A A B B.

(* La distance est independante du sens. *)

Axiom EquiDistantABBA : forall A B : Point, EquiDistant A B B A.

(* Ordre sur les distances. *)


Axiom EquiDistantSegment : forall A B C A' B' C' D' : Point,
	Segment A B C -> 
	EquiDistant A B A' B' -> EquiDistant A C A' C' -> 
	A' <> D' -> ClosedRay A' D' B' -> ClosedRay A' D' C' ->
	Segment A' B' C'.

(* Relation de Chasles. *)

Axiom EquiDistantChasles : forall A B C A' B' C' : Point,
	Segment A C B  -> Segment A' C' B' ->
	EquiDistant A B A' B' -> EquiDistant B C B' C' -> EquiDistant A C A' C'.

Axiom ChaslesEquiDistant : forall A B C A' B' C' : Point,
	Segment A C B -> 
	EquiDistant A B A' B' -> EquiDistant B C B' C' -> EquiDistant A C A' C' ->
	Segment A' C' B'.

(* Inegalite triangulaire. *)


Axiom EquiDistantTriangle : forall A B C A' B' C' D' E': Point,
	Segment A' C' B' -> 
	A' <> E' -> ClosedRay A' E' C' -> ClosedRay A' E' D' ->
	EquiDistant A B A' B' -> EquiDistant B C B' C' -> EquiDistant A C A' D' ->
	Segment A' C' D'.

(* Archimedien. *)

Inductive Archimed (A B : Point) : Point -> Prop :=
	| ArchimedBase : forall C : Point, EquiOriented A C C B -> Archimed A B C
	| ArchimedRec : forall C D : Point, 
				EquiOriented D C A B -> EquiDistant A B D C -> Archimed A B D -> Archimed A B C.

Axiom EquiDistantArchimed : forall A B C : Point,
	ClosedRay A B C -> Archimed A B C.

(* Angles. *)

Axiom EquiDistantAngle : forall A B C D A' B' C' D' : Point,
	ClosedRay A B D -> ClosedRay A' B' D' ->
	EquiDistant A B A' B' -> EquiDistant A C A' C' -> EquiDistant B C B' C' ->
	EquiDistant A D A' D' -> EquiDistant C D C' D'.

(* Somme des angles d'un triangle.*)

Axiom EquiDistantSumAngles : forall A B C D E : Point,
	Clockwise A B C -> Clockwise A C D -> Clockwise A D E ->
	EquiDistant A B D C -> EquiDistant B C A D -> EquiDistant A E C D -> EquiDistant D E C A ->
	Between B A E.

Definition TriangleInequality := fun A B C D E F : Point =>
	exists G : Point, exists H : Point, exists I : Point, exists J : Point, 
	Segment G I H /\ EquiDistant A B G H /\ EquiDistant C D H I /\ 
	Segment G I J /\ EquiDistant E F G J.

End EQUIDISTANT.
