Section CIRCLE.

(* Le compas est le constructeur de cercle a partir d'un point, le centre et de deux points donnant le rayon.*)

Inductive Circle : Set := | Compass : forall C A B : Point, Circle.

(* Les points C, A et B sont appeles points de cosntruction du cercle. *)

Definition Center := fun c : Circle => let (C, _, _) := c in C.

Definition RadiusA := fun c : Circle => let (_, A, _) := c in A.

Definition RadiusB := fun c : Circle => let (_, _, B) := c in B.

(* Le cercle est la representation graphique de la figure formee des points a distance AB du centre C. *)

Definition OnCircle1 (c : Circle) := let (C, A, B) := c in (fun M : Point => EquiDistant C M A B).

(* Une figure est representee par un cercle si l'on sait construire un cercle dont la representaion graphique coincide avec la figure. *)

Definition IsCircle1 (f : Figure) := {c : Circle | forall M : Point, f M <-> OnCircle1 c M}.

(* Deux cercle sont secants si leurs rayons et la distance separant leurs centres satisfont la specification du triangle. *)

Definition TriangleSpec1 := fun A B C D E F : Point =>
	TriangleInequality A B C D E F /\ TriangleInequality C D E F A B /\ TriangleInequality E F A B C D.

Definition SecantCircles1 (c1 c2 : Circle) := 
	Center c1 <> Center c2 /\
	TriangleSpec1 (RadiusA c1) (RadiusB c1) (RadiusA c2) (RadiusB c2) (Center c1) (Center c2).

(* Une droite est un diametre d'un cercle si elle passe par son centre. *)

Definition Diameter (l : Line) (c : Circle) := OnLine l (Center c).

Definition uCircle := Compass Oo Oo Uu.

End CIRCLE.
