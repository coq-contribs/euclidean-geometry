Require Import A1_Plan A2_Orientation A4_Droite A5_Cercle A7_Tactics .
Require Import C1_Distance.

Section CIRCLE_AND_DISTANCE.

Definition Radius := fun c : Circle => let (_, A, B) := c in Distance A B.

Definition OnCircle (c : Circle) := let (C, A, B) := c in (fun M : Point => Distance C M = Distance A B).

Lemma OnCircle1OnCircle : forall c : Circle, forall M : Point,
	OnCircle1 c M -> OnCircle c M.
Proof.
	unfold OnCircle1, OnCircle in |- *; destruct c; simpl in |- *; intros.
	apply DistanceEq; trivial.
Qed.

Lemma OnCircleOnCircle1 : forall c : Circle, forall M : Point,
	OnCircle c M -> OnCircle1 c M.
Proof.
	unfold OnCircle1, OnCircle in |- *; destruct c; simpl in |- *; intros.
	apply EqDistance; trivial.
Qed.

Lemma InterDiameterPointDef : forall (l : Line) (c : Circle),
	Diameter l c ->
	let f := (fun M : Point => OnCircle c M /\ EquiOriented (Center c) M (LineA l) (LineB l)) in
	{M : Point |  f M /\ Unicity M f}.
Proof.
	intros.
	setInterDiameter1 l c ipattern:P.
	 exists P; unfold f in |- *; simpl in |- *; intuition.
	  apply OnCircle1OnCircle; trivial.
	  unfold Unicity in *; intuition.
	    apply Hun; intuition.
	    apply OnCircleOnCircle1; trivial.
Defined.

End CIRCLE_AND_DISTANCE.
