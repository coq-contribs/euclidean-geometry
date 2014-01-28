Require Import A1_Plan A2_Orientation.

Section LINES.

(* La regle est le constructeur de droite a partir de deux points distincts. *)

Inductive Line  : Set := | Ruler : forall A B : Point, A <> B -> Line.

(* Les points A et B sont les points de construction de la droite. *)

Definition LineA := fun l : Line => let (A, _, _) := l in A.

Definition LineB := fun l : Line => let (_, B, _) := l in B.

Definition LineH : forall l : Line, LineA l <> LineB l.
Proof.
	destruct l as (A, B, H); exact H.
Defined.

(* La droite est la representation graphique de la figure formee des points colineaires aux points de construction de la droite. *)

Definition OnLine (l : Line) := let (A,B,_) := l in Collinear A B.

(* Une figure est representee par une droite si l'on sait construire une droite dont la representation graphique coincide avec la figure. *)

Definition IsLine (f : Figure) := {l : Line | forall M : Point, f M <-> OnLine l M}.

(* Deux droites sont paralleles si un demi plan de l'une est inclus dans un demi plan de l'autre. *)

Definition ParallelLines (l1 l2 : Line) := 
	EquiDirected (LineA l1) (LineB l1) (LineA l2) (LineB l2).
	
(* Deux droites sont secantes si elles ne sont pas paralleles. *)

Definition SecantLines (l1 l2 : Line) := ~ParallelLines l1 l2.

Definition lineOoUu := Ruler Oo Uu DistinctOoUu.

End LINES.
