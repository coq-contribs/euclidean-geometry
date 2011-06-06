Section CLOCKWISE.

(* Il existe une relation sur les triplets de points d'orientation dans le sens des aiguilles d'une montre. *)

Parameter Clockwise : Point -> Point -> Point -> Prop.

Definition HalfPlane (A B : Point) : Figure := Clockwise A B.

Definition EquiOriented (A B C D: Point) : Prop  := 
	forall M : Point, Clockwise A B M -> Clockwise C D M.

Definition EquiDirected := fun A B C D : Point =>
	EquiOriented A B C D \/ EquiOriented A B D C \/
	EquiOriented B A C D \/ EquiOriented B A D C \/
	EquiOriented C D A B \/ EquiOriented C D B A \/
	EquiOriented D C A B \/ EquiOriented D C B A.

Definition OpenRay (A B : Point) : Figure  := EquiOriented A B A.

Definition ClosedRay (A B : Point) : Figure  := 
	fun M : Point => EquiOriented A M A B.

Definition Collinear (A B C : Point) := ~Clockwise A B C /\ ~Clockwise B A C.

Definition Between (A B C : Point) :=
	A <> B /\ EquiOriented A B B C.

Definition Segment (A B : Point) :=
	fun M : Point => ClosedRay A B M /\ ClosedRay B A M.

(* Trois points ne peuvent avoir deux orientations a la fois. *)

Axiom ClockwiseAntisym : forall A B C, ~Clockwise A B C \/ ~Clockwise B A C.

(* La relation d'orientation est stable par permutation circulaire. *)

Axiom ClockwisePerm : forall A B C, Clockwise A B C -> Clockwise B C A.

(* Trois points sont necessairement orientes ou alignes. *)

Axiom FourCases : forall A B C,
	Clockwise A B C \/ Clockwise B A C \/ OpenRay A B C \/ OpenRay B A C.
 
(* Etant donne un triangle non degenere, tout point est dans le meme demi plan qu'un sommet par rapport au cote oppose. *)

Axiom FourthPoint : forall A B C D,
	Clockwise A B C ->
	Clockwise A B D \/ Clockwise A D C \/ Clockwise D B C.

(* Trois points colineaires partagent le plan en 2. *)

Axiom ChangeSense : forall A B C D,
	EquiOriented A B C D ->
	Collinear A B C ->
	EquiOriented B A D C.

(* Deux droites paralleles partagent le plan en 3. *)

Axiom ChangeSide : forall A B C D,
	EquiOriented A B C D ->
	A <> B ->
	EquiOriented D C B A.

End CLOCKWISE.
