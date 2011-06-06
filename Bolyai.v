Load "Tactics4_Constructions.v".

Section BOLYAI.

(* Quels que soient les points A B C *)
(* si A B et C ne sont pas colineaires *)
(* alors on sait construire un cercle gamma *)
(* tel que A soit sur gamma et B soit sur gamma et C soit sur gamma. *)

Theorem Bolyai : forall A B C : Point,
~ Collinear A B C ->
{gamma : Circle | OnCircle gamma A /\ OnCircle gamma B /\ OnCircle gamma C}.
Proof.
(* Soient A B C trois points, *)
(* Soit H l'hypothese A , B et C non colineaires, *)
intros.
(* Soit d1 la mediatrice du segment [A,B], *)
setMidLine A B ipattern:d1.
(* Soit d2 la mediatrice du segment [B,C], *)
setMidLine B C ipattern:d2.
(* En utilisant les droites (AB) et (BC) il vient d1 et d2 sont secantes, *)
from (Ruler A B H0, Ruler B C H4) (SecantLines d1 d2).
(* Soit E le point d'intesection de d1 et d2, *)
setInterLines d1 d2 ipattern:E.
(* Soit gamma le cercle de centre E et de rayon EB, *)
setCircle E E B ipattern:gamma.
(* gamma repond a la question, *)
answerIs gamma.
(* de l'hypothese H1 : pour tout point M, si M est sur d1, les distances MA et MB sont egales, il vient les distances EA et EB sont egales, *)
 from H1 (Distance E A = Distance E B).
(* de l'hypothese H5 : pour tout point M, si M est sur d2, les distances MB et MC sont egales, il vient les distances EB et EC sont egales, *)
 from H5 (Distance E B = Distance E C).
Qed.

End BOLYAI.
