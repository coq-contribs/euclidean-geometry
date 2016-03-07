Require Import A1_Plan A2_Orientation A5_Cercle A7_Tactics .
Require Import B7_Tactics .
Require Import C1_Distance C3_SumDistance C5_TriangularInequality C7_Tactics .
Require Import G4_Tactics .
Require Import H1_Triangles.

Section BUILDING_TRIANGLE.

Definition ThirdVertex : forall A B C D E : Point,
	A <> B ->
	Distance A B = Distance D E ->
	Point.
Proof.
	intros.
	setCircle0 D A C ipattern:(gamma).
	setCircle0 E B C ipattern:(gamma').
	setInterCircles gamma gamma' ipattern:(F).
	 simplCircle2; step6 H0.
	 simplCircle2.
	   assert (TriangleSpec A C B C A B).
	  immediate6.
	  step6 H1.
	 exact F.
Defined.

Lemma ThirdVertexTCongruent : forall (A B C D E : Point) (Hab : A <> B) (He : Distance A B = Distance D E),
	TCongruent (Tr A B C ) (Tr D E (ThirdVertex A B C D E Hab He)).
Proof.
	intros; unfold ThirdVertex in |- *.
	destruct (InterCirclesPointDef (Compass D A C) (Compass E B C)) as (F, ((H, (H0, H1)), H2)).
	simplCircle2; unfold TCongruent in |- *; repeat split.
	 immediate6.
	 immediate6.
	 immediate6.
Qed.

Lemma ThirdVertexNotClockwise : forall (A B C D E : Point) (Hab : A <> B) (He : Distance A B = Distance D E),
	~Clockwise D E (ThirdVertex A B C D E Hab He).
Proof.
	intros; unfold ThirdVertex in |- *.
	destruct (InterCirclesPointDef (Compass D A C) (Compass E B C)) as (F, ((H, (H0, H1)), H2)).
	simplCircle2; immediate6.
Qed.

Lemma CollinearTCongruentCollinear : forall A B C D E F : Point,
	Collinear A B C ->
	TCongruent (Tr A B C) (Tr D E F) ->
	Collinear D E F.
Proof.
	unfold TCongruent in |- *; intuition.
	by3SegmentCases1 H.
	 since6 (Segment D E F).
	  apply ChaslesRec.
	    step6 H1; step6 H0; step6 H3; usingChasles2 A C B.
	 since6 (Segment E F D).
	  apply ChaslesRec.
	    step6 H1; step6 H0; step6 H3; usingChasles2 B A C.
	 since6 (Segment F D E).
	  apply ChaslesRec.
	    step6 H1; step6 H0; step6 H3; usingChasles2 C B A.
Qed.

Lemma NotCollinearThirdVertexClockwise : forall (A B C D E : Point) (Hab : A <> B) (He : Distance A B = Distance D E),	~Collinear A B C ->
	Clockwise D (ThirdVertex A B C D E Hab He) E.
Proof.
	intros.
	generalize (ThirdVertexTCongruent A B C D E Hab He).
	unfold ThirdVertex in |- *.
	destruct (InterCirclesPointDef (Compass D A C) (Compass E B C)) as (F, ((H0, (H1, H2)), H3)).
	intro; simplCircle2; by3Cases1 E F D.
	 contradict1 H2 H4.
	 immediate6.
	 elim H; apply (CollinearTCongruentCollinear D E F A B C).
	  immediate6.
	  apply TCongruentSym; exact H4.
Qed.

End BUILDING_TRIANGLE.
