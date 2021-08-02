Definition w {j} (f : RPP j) n := Id' (n - 1) ‖ f.

Definition Ne' n := w Ne n.
Definition Su' n := w Su n.
Definition Pr' n := w Pr n.
Definition Sw' n := w Sw n.

Proposition ex_rewiring : ∀ l l' (p : Permutation l l'),
  ∃ (f : RPP (length l)), «f» l = l'.
Proof.
  intros. induction p.
  - exists Nu. reflexivity.
  - lets f H : IHp.
    exists (Id ‖ f). simpl. rewrite H. reflexivity. 
  - exists (Sw ‖ Id' (length l)).
    simpl. rewrite id'_identity. reflexivity.
  - assert (length l = length l').
    apply Permutation_length. auto. rewrite <- H in IHp2.
    lets f1 H1 : IHp1.
    lets f2 H2 : IHp2.
    exists (f1 ;; f2). subst. auto.
Qed.

Definition cast f n :=
  match (arity f <=? n)%nat with
  | true => f ‖ Id' (n - arity f)
  | false => Id' n
  end.

Open Scope nat_scope.

Lemma arity_cast : ∀ f n, arity (cast f n) = n.
Proof.
  intros. unfold cast.
  remember (arity f <=? n).
  destruct b.
  - simpl. rewrite arity_id'.
    apply le_plus_minus_r. apply Nat.leb_le. auto.
  - apply arity_id'.
Qed.



Fixpoint su n :=
  match n with
  | O => Id 1
  | S n' => Su ;; su n'
  end.

Definition sus := [su 1].
Compute «loading 1 6 sus» [0;3;0;0;0;0;0;0;0;0;0]%Z.



Fixpoint partial (fs : list RPP) n l :=
  match n with
  | O => l
  | S n' => match fs with
    | [] => l
    | f::fs' => partial fs' n' («f» l)
    end
  end.

Definition ifzsw_list := [
  If inc id id ;
  \[3;2;1]\ ;
  If id Sw id ;
  dec ;
  \[3;1;2]\
].

Open Scope Z_scope.

Compute partial ifzsw_list 0 [0;2;0].
Compute partial ifzsw_list 1 [0;2;0].
Compute partial ifzsw_list 2 [0;2;0].
Compute partial ifzsw_list 3 [0;2;0].
Compute partial ifzsw_list 4 [0;2;0].
Compute partial ifzsw_list 5 [0;2;0].

Goal True.
  do 5 (idtac 3).



Definition cast n f :=
  match arity f <=? n with
  | true => f ‖ Id (n - arity f)
  | false => Id n
  end.
Definition wc i n f := cast n (weak i f).


Definition ita f := It f ;; Ne ;; It f ;; Ne.
Definition itr f := It f ;; Ne ;; inv (It f) ;; Ne.

Definition add := itr Su.
Definition sub := inv add.
Definition less := sub ;; id ‖ If Su id id ;; add.

Definition ADD := RE (PR 1 1) (CO (SU 1 1) [PR 1 3]).
Definition PRE := RE (ZE 0) (PR 2 2).
Definition SUB := RE (PR 1 1) (CO PRE [PR 1 3]).
Definition MUL := RE (ZE 1) (CO ADD [PR 1 3;PR 3 3]).

Definition pad f l := evaluate f (l ++ repeat 0%Z (arity f - length l)).

Fixpoint count f : nat :=
  match f with
  | Id _ | Ne | Su | Pr | Sw => 1
  | Co f g => count f + count g
  | Pa f g => count f + count g
  | It f => 1 + count f
  | If f g h => 1 + count f + count g + count h
  end.

Compute count (convert ADD).

Compute pad (convert PRE) [0;5]%Z.
Compute pad (convert ADD) [0;3;4]%Z.
Compute pad (convert SUB) [0;2;5]%Z.
Compute pad (convert MUL) [0;2;2]%Z.

Lemma zero_Z_to_nat : ∀ x, O = Z.to_nat x → x = 0 ∨ ∃ p, x = Z.neg p.
Proof.
  intros. destruct x.
  - auto.
  - right. lia.
  - eauto.
Qed.

Lemma cu_cp2 : ∀ n x y, (x,y) = cu_iter n → cp2 x y = 2*n.
Proof.
  intros. gen x y. induction n.
  - intros. unfold cu_iter in H. simpl in H.
    injection H. intros. subst.
    unfold cp2. reflexivity.
  - intros. lets (X & Y & H0) : ex_pair (cu_iter n).
    destruct Y.
    + assert ((x,y) = (0, X+1)).
      { rewrite H. unfold cu_iter in *. simpl.
        rewrite H0. simpl. f_equal. lia. }
      injection H1. intros. subst.
      symmetry in H0. apply IHn in H0.
      replace (2 * S n) with (S (S (2 * n))).
      rewrite <- H0.
      unfold cp2. lia. lia.
    + assert ((x,y) = (S X, Y)).
      { rewrite H. unfold cu_iter in *. simpl.
        rewrite H0. reflexivity. }
      injection H1. intros. subst.
      symmetry in H0. apply IHn in H0.
      replace (2 * S n) with (S (S (2 * n))).
      rewrite <- H0.
      unfold cp2. lia. lia.
Qed.

Lemma inc_def : ∀ x y, 0 <= x → «inc» [x;y] = [x;y+x].
Proof.
  intros. destruct x.
  - simpl. f_equal. f_equal. lia.
  - apply inc_pos.
  - contradiction.
Qed.



Compute «ifzsw» [0;-3;0].

Goal ∀ n m, 0 <= n → «inc» [n+123;m+34;123;32] = [n+123;m+34+n+123;123;32].
Proof.
  intros. rewrite longer. simpl firstn. simpl skipn.
  rewrite inc_def. simpl. f_equal. f_equal. lia. lia.
Qed.

Lemma nth_app : ∀ X n (l l' : list X) d, length l ≤ n →
  nth n (l ++ l') d = nth (n - length l) l' d.
Proof.
  intros. replace n with (length l + (n - length l)).
  rewrite nth_sum. rewrite skipn_app.
  
  destruct l'.

 rewrite nth_middle.


replace n with (length l + (n - length l)).



assert (∃ l0 x y l1, length l0 = n ∧ l = ((l0++[x])++[y])++l1).
    exists (firstn n l) (nth n l 0) (nth (1+n) l 0) (skipn (2+n) l).
    split. rewrite firstn_length. lia.
    rewrite <- firstn_Sn. rewrite <- firstn_Sn.
    replace (1+(1+n))%nat with (2+n)%nat. rewrite firstn_skipn. auto.
    all: try lia.

    lets (l0 & x & y & l1 & H1 & H2) : H0.
    assert (l = (l0 ++ x :: (y :: l1))).
    rewrite H2. rewrite <- !app_assoc. auto.
    rewrite id_swap_def. rewrite IHn.
    replace (firstn n l) with l0.
    replace (nth (1 + n) l 0) with y.
    replace (nth n l 0) with x.
    replace (skipn (2 + n) l) with l1.
    replace (nth n (l0 ++ [y; x] ++ l1) 0) with y.
    replace (firstn n (l0 ++ [y; x] ++ l1)) with l0.
    replace (skipn (S n) (l0 ++ [y; x] ++ l1)) with (x::l1).
    replace (nth (S n) l 0) with y.
    replace (firstn (S n) l) with (l0++[x]).
    replace (skipn (S (S n)) l) with l1.
    rewrite <- app_assoc. reflexivity.

    rewrite H3. rewrite skipn_app.
    rewrite skipn_all2.
    replace (S (S n) - length l0)%nat with 2%nat.
    reflexivity. lia. lia.

    rewrite H3. rewrite firstn_app.
    rewrite firstn_all2.
    replace (S n - length l0)%nat with 1%nat.
    reflexivity. lia. lia.

    rewrite H3. rewrite nth_middle.

rewrite nth_app.
    rewrite H3. admit.
    rewrite H3. admit.
    admit. rewrite firstn_app. rewrite firstn_all2.
    replace (n-length l0)%nat with O. rewrite firstn_O.
    rewrite app_nil_r. reflexivity. lia. lia.
    admit. rewrite H3. admit. rewrite H3. admit.
    rewrite H3. admit. rewrite H3. admit.
    simpl. rewrite app_length. admit. lia.
Admitted.

Definition l := [0;1;2;3;4;5;6;7].
Compute «\[S 4; 0]\%nat» l.
Compute nth (S 4) l 0 :: 0 :: part 1 (S 4) l ++ skipn (S (S 4)) l.



Open Scope nat.
Lemma firstn_Sn : ∀ X n (l : list X) d, n < length l →
  firstn (1+n) l = firstn n l ++ [nth n l d].
Proof.
  intros. lets (l0 & l1 & H0 & H1) : nth_split d H.
  rewrite H0. rewrite !firstn_app.
  rewrite firstn_all2.
  replace (1 + n - length l0) with (S (n - length l0)).
  rewrite firstn_cons.
  replace (n - length l0) with 0. simpl.
  rewrite <- H1. rewrite nth_middle. rewrite firstn_all2.
  f_equal. rewrite app_nil_r. reflexivity. all:lia.
Qed.

Open Scope nat.
Lemma nth_sum : ∀ X n m (l : list X) d,
  nth (n+m) l d = nth n (skipn m l) d.
Proof.
  intros. gen l. induction m.
  - intros. simpl. f_equal. auto.
  - intros. replace (n + S m) with (S (n + m)).
    rewrite nth_Sn. rewrite IHm.
    destruct l. simpl. rewrite skipn_nil.
    destruct n; auto. reflexivity. lia.
Qed.

Fixpoint strict (F : PRF) : Prop :=
  match F with
  | ZE n => True
  | SU i n => True
  | PR i n => True
  | CO F Gs => strict F ∧ Forall (λ G, strict G) Gs ∧
    ARITY F = length Gs ∧ Forall (λ G, ARITY G = list_max (map ARITY Gs) ) Gs
  | RE F G => strict F ∧ strict G ∧ ARITY G = 2+ARITY F
  end.

Lemma le_ind : ∀ n (P : nat → Prop),
  (∀ n, (∀ m, m < n → P m) -> (∀ m, m ≤ n → P m)) -> P n.
Proof.
  intros. induction n as [n IHn] using lt_wf_ind.
  apply H with (n:=n); easy.
Qed.

Lemma PRF_ind2 :
  ∀ P : PRF → Prop,
  (∀ n, P (ZE n)) →
  (∀ i n, P (SU i n)) →
  (∀ i n, P (PR i n)) →
  (∀ F, P F → ∀ Gs, (∀ G, In G Gs → P G) → P (CO F Gs)) →
  (∀ F, P F → ∀ G : PRF, P G → P (RE F G)) →
  ∀ p : PRF, P p.
Proof.
  intros. induction p; auto.  
  induction Gs.
  - intros. apply H2; easy.
  - intros. apply H2. easy.
    simpl. intros G [].
    + rewrite <- H4.
    intros. simpl in H4.

Theorem theorem_5 : ∀ F l x, thesis F l x.
Proof.
  intros. induction F.
  - apply thesis_ze.
  - apply thesis_su.
  - apply thesis_pr.
  - admit.
  - 
Admitted.

Compute «convert ADD» (0 :: ↑↑[3;4]%nat ++ zeros (anc ADD)).
Compute 0 + ↑(EVALUATE ADD [3;4]%nat) :: ↑↑[3;4]%nat ++ zeros (anc ADD).
Compute arity (convert ADD).
Compute (1 + 2 + anc ADD)%nat.

Lemma perm1 : ∀ n x l, (n < length l)%nat → «\[1+n;0]%nat\» (x::l) =
  l^[n] ++ x :: l^[0,n] ++ l^[1+n,∞].
Proof.
  intros. unfold perm. simpl prepare. simpl rev.
  replace (n+0)%nat with n. remember (S n) as m. simpl call_list.
  segment. rewrite id_def. rewrite call_def. subst. all: liast.
Qed.

Definition pad f l :=
  evaluate f (l ++ repeat 0%Z (arity f - length l)).

Open Scope Z.
Compute «convert ADD» (0 :: ↑↑[3;4]%nat ++ zeros (anc ADD)).
Compute «convert MUL» (0 :: ↑↑[2;3]%nat ++ zeros (anc MUL)).
Compute (convert MUL).
Compute arity (convert MUL).
Compute 0 + ↑(EVALUATE ADD [3;4]%nat) :: ↑↑[3;4]%nat ++ zeros (anc ADD).
Compute arity (convert ADD).
Compute (1 + 2 + anc ADD)%nat.


Open Scope bool.
Fixpoint strictb (F : PRF) : bool :=
  match F with
  | ZE n => true
  | SU i n => i <? n
  | PR i n => i <? n
  | CO F Gs => strictb F && forallb (λ G, strictb G) Gs &&
    (ARITY F =? length Gs) && forallb (λ G, ARITY G =? ARITY (CO F Gs)) Gs
  | RE F G => strictb F && strictb G && (ARITY G =? 2+ARITY F)
  end.

Lemma arity_conv_co_nil : ∀ F, strict F →
  arity (convert (CO F [])) = arity (convert F).
Proof.
  intros. simpl.
  assert (H0 := ARITY_le_arity H). remember (arity (convert F)).
  destruct n. lia. lia.
Qed.

Lemma arity_conv_co_cons : ∀ F G, strict F →
  ARITY G + arity (convert F) ≤ arity (convert (CO F [G])).
Admitted.

  intros. destruct Gs.
  - unfold anc. inverts H. rewrite arity_conv_co_nil.
    assert (H0 := arity_conv_co_cons G H2). simpl ARITY.
    rewrite max_l. rewrite <- Nat.pred_lt_mono. lia.
    simpl convert. rewrite max_l.
    rewrite arity_co_def. rewrite Nat.max_le_iff. left.
    simpl. autorewrite with arith_base. segment. simpl. inverts H.
    apply Forall_inv in H3. apply Forall_inv in H5. simpl in *. 
  unfold anc.
  assert (arity (convert (CO F Gs)) < arity (convert (CO F (G :: Gs)))).
  { admit. }
  assert (ARITY (CO F Gs) = ARITY (CO F (G::Gs))).
  { 
  rewrite H1.
  assert (ARITY (CO F Gs) < arity (convert (CO F Gs))).
  { apply ARITY_le_arity. apply strict_cons with (G:=G). easy. }
  lia.


Lemma list_max_ge : ∀ l n, In n l → n ≤ list_max l.
Proof.
  intros. induction l.
  - false.
  - simpl in *. destruct H.
    + subst. lia.
    + apply Nat.max_le_iff. right. apply IHl. easy.
Qed.

Open Scope nat.
Lemma strict_cons : ∀ F G Gs, strict (CO F (G :: Gs)) → strict (CO F Gs).
Proof.
  intros. inverts H.
  apply strCO.
  - easy.
  - apply Forall_inv_tail in H3. easy.
  - simpl in H4. lia.
  - apply Forall_inv_tail in H5.
    destruct Gs.
    + simpl. easy.
    + assert (ARITY (CO F (G :: p :: Gs)) = ARITY (CO F (p :: Gs))).
      { simpl. assert (H6 := H5).
        apply Forall_inv in H5. apply Forall_inv_tail in H6.
        simpl in *. lia. }
      rewrite H in H5. easy.
Qed.

Lemma arity_co_cons : ∀ F G Gs, Gs ≠ [] → strict (CO F (G::Gs)) →
  ARITY (CO F Gs) = ARITY (CO F (G::Gs)).
Proof.
  intros. assert (H1 := strict_cons H0). inverts H0. inverts H1.
  destruct Gs. false.
  apply Forall_inv_tail in H7. apply Forall_inv in H7.
  apply Forall_inv in H10. lia.
Qed.

Lemma anc_co_lt1 : ∀ F G Gs, strict (CO F (G :: Gs)) →
  anc (CO F Gs) < anc (CO F (G :: Gs)).
Admitted.

Lemma anc_co_lt2 : ∀ F G Gs, strict (CO F (G :: Gs)) →
  anc G < anc (CO F (G :: Gs)).
Admitted.

Open Scope Z.
Goal ∀ F Gs l n,
  Forall (λ G, strict G) Gs →
  Forall (λ G, ARITY G = ARITY (CO F Gs)) Gs →
  Forall (λ G, thesis G l 0) Gs →
  ARITY (CO F Gs) = length l →
  anc (CO F Gs) ≤ n →
  «co_loading (ARITY (CO F Gs)) (map convert Gs)»
    (↑↑l ++ repeat 0%Z n) =
  ↑↑map (λ G, EVALUATE G l) Gs ++ ↑↑l ++ repeat 0%Z (n - length Gs).
Proof.
  intros. gen l n. induction Gs.
  - intros. simpl. autorewrite with arith_base. reflexivity.
  - intros. simpl co_loading. segment.
    assert (list_max (map ARITY Gs) ≤ ARITY a).
    { apply Forall_inv in H0.
      rewrite H0. simpl. lia. }
    simpl in H2. rewrite max_l in *.
    pose (anc_co_lt1 F a Gs). pose (anc_co_lt2 F a Gs).
    asserts_rewrite (
      « \ [ARITY a] \ » (↑↑ l ++ repeat 0 n) =
      0 :: ↑↑l ++ repeat 0 (n-1) ).
    { unfold perm. simpl call_list. rewrite Nat.add_0_r.
      rewrite call_def.
      replace ((↑↑ l ++ repeat 0 n) ^[ ARITY a])
      with [0].
      replace ((↑↑ l ++ repeat 0 n) ^[ 0, ARITY a])
      with (↑↑l).
      replace ((↑↑l ++ repeat 0 n) ^[ 1 + ARITY a, ∞ ])
      with (repeat 0 (n-1)).
      reflexivity.
      rewrite skipn_app. rewrite skipn_all2. rewrite app_nil_l.
      rewrite repeat_skipn. f_equal. f_equal. rewrite map_length.
      lia. rewrite map_length. lia.
      rewrite splice_app. rewrite splice_all. rewrite splice_gt.
      rewrite app_nil_r. reflexivity.
      rewrite map_length. lia. rewrite map_length. lia.
      rewrite splice_app. rewrite splice_all2. rewrite app_nil_l.
      rewrite map_length.
      replace (1 + ARITY a - length l)%nat with (1+(ARITY a - length l))%nat.
      replace (ARITY a - length l)%nat with O.
      rewrite splice_nth with (d:=0). f_equal.
      generalize (anc (CO F (a :: Gs))). intros.
      destruct n. reflexivity. reflexivity.
      rewrite repeat_length.
      lia. lia. lia. rewrite map_length. lia.
      rewrite app_length. rewrite map_length.
      rewrite repeat_length. lia. }
    rewrite thesis_le.
    rewrite pa_def. simpl. f_equal.
    destruct Gs. reflexivity.
    assert (ARITY a = ARITY p).
    { pose (Forall_inv H0) as H5. simpl in H5.
      pose (Forall_inv_tail H0) as H6.
      apply Forall_inv in H6. simpl in H6.
      lia. }
    assert (ARITY (CO F (p::Gs)) = ARITY a).
    { rewrite H5. apply Forall_inv_tail in H0.
      apply Forall_inv in H0. rewrite H0. simpl. lia. }
    remember (p::Gs) as Gs'.
    rewrite <- H6.
    replace (n - S (length Gs'))%nat with ((n - 1) - length Gs')%nat.
    apply IHGs.
    apply Forall_inv_tail in H. easy.
    apply Forall_inv_tail in H0.
    assert (ARITY (CO F Gs') = ARITY (CO F (a::Gs'))).
    { simpl in *. lia. } rewrite H7. apply H0.
    apply Forall_inv_tail in H1. easy.
    lia. lia. lia.
    apply Forall_inv in H1. easy.
    lia.
    apply Forall_inv in H. easy.
    easy. easy. easy.
Qed.


apply Forall_inv_tail in H8.
        apply Forall_inv in H8. rewrite H8. simpl. lia.


      rewrite repeat_spec with (n:=anc (CO F (a :: Gs)))(x:=0).
      reflexivity. apply nth_in_or_default.
      generalize (repeat 0 (anc (CO F (a :: Gs)))). intros.
      destruct l0. reflexivity. simpl.

rewrite max_l.

  x + ↑(EVALUATE F l) :: ↑↑l ++ repeat 0 (anc F).


Admitted.