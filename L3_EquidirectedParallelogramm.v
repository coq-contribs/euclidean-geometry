Require Import A1_Plan A2_Orientation A7_Tactics .
Require Import B7_Tactics .
Require Import C1_Distance C7_Tactics .
Require Import E4_Tactics .
Require Import F2_MarkSegment F5_Tactics .
Require Import G1_Angles .
Require Import J2_MidPoint J4_Tactics .
Require Import K3_Tactics .
Require Import L1_Parallelogramm L2_StrictParallelogramm.

Section EQUIDIRECTED_PARALLELOGRAMM.

Lemma FlatParallelogramm : forall (A B C D : Point)  (H : Parallelogramm A B C D),
	Collinear A B (PCenter A B C D H) ->
	EquiOriented A B D C.
Proof.
	intros.
	assert (H1 := PCenterBetweenAC A B C D H).
	assert (H2 := PCenterBetweenBD A B C D H).
	assert (H3 := ParallelogrammTCongruentAKBCKD A B C D H).
	from10 H3 (Distance A B = Distance C D).
	 from10 H3  (Distance A (PCenter A B C D H) = Distance C (PCenter A B C D H)).
	  from10 H3 (Distance (PCenter A B C D H) B = Distance (PCenter A B C D H) D).
	   by3SegmentCases1 H0.
	    since10 (Segment D C (PCenter A B C D H)).
	     usingChaslesRec2.
	       step10 H6.
	       step10 H5.
	       step10 H4.
	       usingChasles2 A (PCenter A B C D H) B.
	     unfold EquiOriented in |- *; intros.
	       step10 H8.
	       left; step10 H2.
	       right; step10 H7.
	    since10 (Segment D (PCenter A B C D H) C).
	     usingChaslesRec2.
	       step10 H6.
	       step10 H5.
	       step10 H4.
	       usingChasles2 (PCenter A B C D H) A B.
	     unfold EquiOriented in |- *; intros.
	       step10 H7.
	      step10 H4.
	      left; step10 H2.
	        right; step10 H8.
	    since10 (Segment (PCenter A B C D H) C D).
	     usingChaslesRec2.
	       step10 H6.
	       step10 H5.
	       step10 H4.
	       usingChasles2 A B (PCenter A B C D H).
	     unfold EquiOriented in |- *; intros.
	       step10 H7.
	      step10 H4.
	      left; step10 H2.
	        left; step10 H8.
Qed.

Lemma PCenterMidPoint : forall (A B C D : Point)  (H : Parallelogramm A B C D) (Hac : A <> C),
	PCenter A B C D H = MidPoint A C Hac.
Proof.
	intros A B C D H Hac; unfold PCenter in |- *; dependent inversion H.
	byDefEqPoint10.
Qed.

Lemma ParallelogrammOpenRayAB : forall (A B C D E : Point)  (H : StrictParallelogramm A B C D) (Hek : E <>  (SPCenter A B C D H)),
	 OpenRay A B E ->
	OpenRay C D (SymmetricPoint E  (SPCenter A B C D  H) Hek).
Proof.
	intros A B C D E H; DestructSP11 H.
	assert (Habc := StrictParallelogrammClockwiseABC A B C D H).
	intros.
	assert (Hab : A <> B).
	 immediate10.
	 assert (Hcd : C <> D).
	  apply (StrictParallelogrammDistinctCD A B C D H).
	  assert (Hae : A <> E).
	   step10 H2.
	   setMidPoint9 A C ipattern:K.
	     since10 (PCenter A B C D H0 = K).
	    rewrite (PCenterMidPoint A B C D H0 H3); immediate10.
	    generalize Hek; rewrite H6; clear Hek; intro Hek.
	      assert (H7 := ParallelogrammTCongruentAKBCKD A B C D H0).
	      rewrite H6 in H7.
	      assert (H8 := StrictParallelogrammClockwiseCDK A B C D H); simpl in H8.
	      rewrite H6 in H8.
	      setSymmetricPoint5 E K ipattern:F; fold F in |- *.
	      assert (Hef : E <> F).
	     immediate10.
	     since10 (Parallelogramm A E C F).
	      apply (Pllgm A E C F H3 Hef).
	        fold K in |- *; immediate10.
	      assert (Haec : Clockwise A E C).
	       step10 H1.
	       pose (H12 := SPDef H11 Haec).
	         assert (Hcf : C <> F).
	        apply (StrictParallelogrammDistinctCD A E C F H12).
	        since10 (PCenter A E C F H11 = K).
	         rewrite (PCenterMidPoint A E C F H11 H3); immediate10.
	         assert (H14 := ParallelogrammTCongruentAKBCKD A E C F H11).
	           rewrite H13 in H14.
	           assert (H15 := StrictParallelogrammClockwiseCDK A E C F H12).
	           simpl in H15.
	           rewrite H13 in H15.
	           from10 H7 (CongruentAngle K C D K C F).
	            step10 H14.
	            step10 H2.
	          step10 H16.
Qed.

Lemma ParallelogrammOpenRayBA : forall (A B C D E : Point)  (H : StrictParallelogramm A B C D) (Hek : E <>  (SPCenter A B C D H)),
	 OpenRay B A E ->
	OpenRay D C (SymmetricPoint E  (SPCenter A B C D H) Hek).
Proof.
	intros A B C D E H; DestructSP11 H.
	intros; assert (Hdab : Clockwise D A B).
	 apply (StrictParallelogrammClockwiseDAB A B C D H).
	 inversion H0.
	   assert (Hba : B <> A).
	  apply sym_not_eq; apply (StrictParallelogrammDistinctAB A B C D H).
	  assert (Hdc : D <> C).
	   apply sym_not_eq; apply (StrictParallelogrammDistinctCD A B C D H).
	   assert (Hbe : B <> E).
	    step10 H2.
	    setMidPoint9 B D ipattern:K.
	      since10 (PCenter A B C D H0 = K).
	     rewrite (PCenterMidPoint A B C D H0 Hac); immediate10.
	     generalize Hek; rewrite H6; clear Hek; intro Hek.
	       assert (H7 := ParallelogrammTCongruentAKBCKD A B C D H0).
	       rewrite H6 in H7.
	       assert (H8 := StrictParallelogrammClockwiseCDK A B C D H).
	       simpl in H8; rewrite H6 in H8.
	       setSymmetricPoint5 E K ipattern:F; fold F in |- *.
	       assert (Hfe : F <> E).
	      immediate10.
	      since10 (Parallelogramm B F D E).
	       apply (Pllgm B F D E Hbd Hfe).
	         fold K in |- *; immediate10.
	       since10 (StrictParallelogramm B F D E).
	        apply (ClockwiseCDAStrictParallelogramm B F D E H11); step10 H2.
	        clear H11; DestructSP11 H12.
	          assert (Hdf : D <> F).
	         apply sym_not_eq; apply (StrictParallelogrammDistinctBC B F D E H12).
	         since10 (PCenter B F D E H11 = K).
	          rewrite (PCenterMidPoint B F D E H11 Hbd); immediate10.
	          assert (H15 := ParallelogrammTCongruentBKCDKA B F D E H11).
	            rewrite H14 in H15.
	            assert (H16 := StrictParallelogrammClockwiseBCK B F D E H12).
	            simpl in H16; rewrite H14 in H16.
	            since10 (CongruentAngle C D K F D K).
	           step10 H7.
	             step10 H15.
	             step10 H2.
	           step10 H17.
Qed.

Lemma StrictParallelogrammEquiOriented : forall A B C D : Point, 
	StrictParallelogramm A B C D  ->  EquiOriented B A C D.
Proof.
	unfold EquiOriented in |- *; intros; DestructSP11 ipattern:H.
	assert (Hcd : C <> D).
	 apply (StrictParallelogrammDistinctCD A B C D H).
	 since10 (Between A (PCenter A B C D H1) C).
	  apply (PCenterBetweenAC A B C D H1).
	  since10 (Between B (PCenter A B C D H1) D).
	   apply (PCenterBetweenBD A B C D H1).
	   setFourPointsInter4 A B M (PCenter A B C D H1) ipattern:J.
	    apply (StrictParallelogrammClockwiseABK A B C D H).
	    setSymmetricPoint5 J (PCenter A B C D H1) ipattern:L.
	      from10 H10 (Between L (PCenter A B C D H1) M).
	     by2Cases1 H6.
	      since10 (OpenRay C D L).
	       unfold L in |- *; apply (ParallelogrammOpenRayAB A B C D J H); immediate10.
	       step10 H13.
	         step10 H11.
	         right; step10 H3.
	         right; step10 H7.
	         left; step10 H12.
	      since10 (OpenRay D C L).
	       unfold L in |- *; apply (ParallelogrammOpenRayBA A B C D J H);  immediate10.
	       step10 H13.
	         step10 H11.
	         left; step10 H4.
	         left; step10 H7.
	         right; step10 H12.
Qed.

Lemma ParallelogrammEquiDirected : forall A B C D : Point, 
	Parallelogramm A B C D ->  EquiDirected A B C D.
Proof.
	intros; by3Cases1 ipattern:A ipattern:B (PCenter A B C D H).
	 since10 (EquiOriented B A C D).
	  since10 (StrictParallelogramm A B C D).
	   apply (ClockwiseABKStrictParallelogramm A B C D H); immediate10.
	   apply (StrictParallelogrammEquiOriented A B C D H1).
	  canonize1; intuition.
	 inversion H.
	   since10 (MidPoint A C Hac = MidPoint C A (sym_not_eq Hac)).
	  since10 (MidPoint D B (sym_not_eq Hbd) = MidPoint B D Hbd).
	   since10 (Parallelogramm D C B A).
	    apply (Pllgm D C B A (sym_not_eq Hbd) (sym_not_eq Hac)).
	      step10 H2.
	      step10 H0.
	    since10 (PCenter A B C D H = PCenter D C B A H4).
	     rewrite (PCenterMidPoint A B C D H Hac).
	       rewrite (PCenterMidPoint D C B A H4 (sym_not_eq Hbd)).
	       step10 H0.
	     since10 (StrictParallelogramm D C B A).
	      apply (ClockwiseCDKStrictParallelogramm D C B A H4).
	        step10 H5.
	      since10 (EquiOriented C D B A).
	       apply (StrictParallelogrammEquiOriented D C B A H6).
	       canonize1; intuition.
	 since10 (EquiOriented A B D C).
	  apply (FlatParallelogramm A B C D H H1).
	  canonize1; intuition.
Qed.

End EQUIDIRECTED_PARALLELOGRAMM.

