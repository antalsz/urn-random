From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Coq.ZArith.ZArith.
Require Import Haskell Option arith_util.

Open Scope N_scope.
Open Scope haskell_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* FIXME should be Word32 *)
Definition Word := N.
Bind Scope N_scope with Word.

Definition Weight : Type := Word.
Bind Scope N_scope with Weight.

Record Size  : Type := MkSize  { getSize  : Word }.
Record Index : Type := MkIndex { getIndex : Word }.

Definition succSize  : Size -> Size := MkSize ∘ N.succ ∘ getSize.
Definition predSize' : Size -> Size := MkSize ∘ N.pred ∘ getSize.

Definition evenSize : Size -> bool := N.even ∘ getSize.
Definition div2Size : Size -> Size := MkSize ∘ N.div2 ∘ getSize.

Arguments succSize  !sz.
Arguments predSize' !sz.
Arguments evenSize  !sz.
Arguments div2Size  !sz.

Inductive BTree (A : Type) : Type :=
  | BLeaf   of A
  | BNode   of WTree A & WTree A
with      WTree (A : Type) : Type :=
  | MkWTree of Weight & BTree A.

Arguments BLeaf   {A} _.
Arguments BNode   {A} _ _.
Arguments MkWTree {A} _ _.

Definition weight {A} (wt : WTree A) : Weight  := match wt with MkWTree w _  => w  end.
Definition btree  {A} (wt : WTree A) : BTree A := match wt with MkWTree _ bt => bt end.

Notation WLeaf w a   := (MkWTree w (BLeaf a)).
Notation WNode w l r := (MkWTree w (BNode l r)).

Record Urn (A : Type) : Type := MkUrn { size  : Size
                                      ; wtree : WTree A }.
Arguments MkUrn {A} _ _.
Arguments size  {A} _.
Arguments wtree {A} _.

Fixpoint bsample {A} (bt : BTree A) (i : Index) : A :=
  match bt with
    | BLeaf a => a
    | BNode (MkWTree wl l) (MkWTree _ r) =>
      let: MkIndex i' := i
      in if i' <? wl
         then bsample l i
         else bsample r (MkIndex (i' - wl))
  end.

Definition sample {A} : WTree A -> Index -> A := bsample ∘ btree.

Definition foldWTree {A} {B}
                     (fLeaf  : Weight -> A -> B)
                     (fLeft  : Weight -> B -> WTree A -> B)
                     (fRight : Weight -> WTree A -> B -> B)
                       : Size -> WTree A -> B :=
  fix go path wt :=
      match wt with
        | WLeaf w a   => fLeaf w a
        | WNode w l r => let path' := div2Size path
                         in if evenSize path
                            then fLeft  w (go path' l) r
                            else fRight w l            (go path' r)
      end.

Definition insert {A} (w' : Weight) (a' : A) (u : Urn A) : Urn A :=
  let: MkUrn size wt := u
  in MkUrn (succSize size)
       $ foldWTree (fun w a     => WNode (w + w') (WLeaf w a) (WLeaf w' a'))
                   (fun w l' r  => WNode (w + w') l' r)
                   (fun w l  r' => WNode (w + w') l  r')
                   size wt.

Definition uninsert {A} (u : Urn A) : Weight * A * Weight * option (Urn A) :=
  let: MkUrn size wt := u
  in match foldWTree
             (fun w a       => (w, a, 0, None))
             (fun w ul' r   => match ul' with
                                 | (w', a', lb, Some l') =>
                                     (w', a', lb, Some $ WNode (w - w') l' r)
                                 | (w', a', lb, None)    => 
                                     (w', a', lb, Some r)
                               end)
             (fun w l   ur' => match ur' with
                                 | (w', a', lb, Some r') =>
                                     (w', a', lb + weight l, Some $ WNode (w - w') l r')
                                 | (w', a', lb, None)    =>
                                     (w', a', lb + weight l, Some l)
                               end)
             (predSize' size) wt
     with
       | (w', a', lb, mt) => (w', a', lb, omap (MkUrn $ predSize' size) mt)
     end.


Definition update {A} (upd : Weight -> A -> Weight * A)
                        : WTree A -> Index -> Weight * A * Weight * A * WTree A :=
  fix go wt ix :=
    let: MkIndex i := ix
    in match wt with
         | WLeaf w a =>
             let: (wNew, aNew) := upd w a
             in (w, a, wNew, aNew, WLeaf wNew aNew)
         | WNode w (MkWTree wl _ as l) r =>
             if i <? wl
             then match go l (MkIndex i) with
                    | (wOld, aOld, wNew, aNew, l') =>
                        (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l' r)
                  end
             else match go r (MkIndex $ i - wl) with
                      (wOld, aOld, wNew, aNew, r') =>
                        (wOld, aOld, wNew, aNew, WNode (w-wOld+wNew) l r')
                  end
       end.

Definition replace {A} (wNew : Weight) (aNew : A)
                     : WTree A -> Index -> Weight * A * WTree A :=
  fix go wt ix :=
    let: MkIndex i := ix
    in match wt with
         | WLeaf w a => 
             (w, a, WLeaf wNew aNew)
         | WNode w (MkWTree wl _ as l) r =>
             if i <? wl
             then match go l (MkIndex i) with
                    | (w', a', l') => (w', a', WNode (w-w'+wNew) l' r)
                  end
             else match go r (MkIndex $ i-wl) with
                    | (w', a', r') => (w', a', WNode (w-w'+wNew) l r')
                  end
       end.

(******************************************************************************)

Definition Size_eq (s1 s2 : Size) : bool := getSize s1 == getSize s2.
Arguments Size_eq !s1 !s2 /.

Lemma Size_eqP : Equality.axiom Size_eq.
Proof.
  move=> [p1] [p2] /=; case Heq: (p1 == p2); constructor.
  - by move: Heq => /eqP->.
  - by contradict Heq; apply/Bool.not_false_iff_true/eqP; case: Heq.
Qed.

Definition Size_eqMixin := EqMixin Size_eqP.
Canonical Size_eqType := EqType Size Size_eqMixin.

Scheme BTree_WTree_rec := Induction for BTree Sort Set
  with WTree_BTree_rec := Induction for WTree Sort Set.

Scheme BTree_WTree_rect := Induction for BTree Sort Type
  with WTree_BTree_rect := Induction for WTree Sort Type.

Scheme BTree_WTree_ind := Induction for BTree Sort Prop
  with WTree_BTree_ind := Induction for WTree Sort Prop.

Fixpoint WTree_deep_rect (A : Type) (P : WTree A -> Type)
                         (leaf : forall (w : Weight) (a : A), P (WLeaf w a))
                         (node : forall (w : Weight)
                                        (l : WTree A) (IHl : P l)
                                        (r : WTree A) (IHr : P r),
                                   P (WNode w l r))
                         (wt : WTree A) : P wt :=
  match wt with
    | WLeaf w a   => leaf w a
    | WNode w l r => node w
                          l (WTree_deep_rect leaf node l)
                          r (WTree_deep_rect leaf node r)
  end.

Definition WTree_deep_rec : forall (A : Type) (P : WTree A -> Set)
                                   (leaf : forall (w : Weight) (a : A), P (WLeaf w a))
                                   (node : forall (w : Weight)
                                                  (l : WTree A) (IHl : P l)
                                                  (r : WTree A) (IHr : P r),
                                             P (WNode w l r))
                                   (wt : WTree A),
                              P wt
  := WTree_deep_rect.

Definition WTree_deep_ind : forall (A : Type) (P : WTree A -> Prop)
                                   (leaf : forall (w : Weight) (a : A), P (WLeaf w a))
                                   (node : forall (w : Weight)
                                                  (l : WTree A) (IHl : P l)
                                                  (r : WTree A) (IHr : P r),
                                             P (WNode w l r))
                                   (wt : WTree A),
                              P wt
  := WTree_deep_rect.

(******************************************************************************)

Lemma Size_pred_succ (s : Size) : predSize' (succSize s) = s.
Proof. by case: s => [s]; rewrite /predSize' /succSize /= N.pred_succ. Qed.

Lemma Size_succ_pred_or (s : Size) : s = MkSize 0 \/ succSize (predSize' s) = s.
Proof.
  case: s => [s]; rewrite /succSize /predSize' /=.
  by case: s; [left | right; rewrite N.succ_pos_pred].
Qed.

Lemma Size_succ_pred (s : Size) : s <> MkSize 0 -> succSize (predSize' s) = s.
Proof.
  case: s => [s] neq_1; rewrite /succSize /predSize' /= N.succ_pred //=.
  by contradict neq_1; f_equal.
Qed.

(******************************************************************************)

Fixpoint WTree_count {A} (wt : WTree A) : positive :=
  match wt with
    | WLeaf _ _   => 1
    | WNode _ l r => WTree_count l + WTree_count r
  end%positive.

Fixpoint WTree_sum_leaf_weights {A} (wt : WTree A) : N :=
  match wt with
    | WLeaf w _   => w
    | WNode _ l r => WTree_sum_leaf_weights l + WTree_sum_leaf_weights r
  end%num.

Fixpoint WTree_weights_match {A} (wt : WTree A) : bool :=
  match wt with
    | WLeaf w _   => true
    | WNode w l r => [&& (w == WTree_sum_leaf_weights l + WTree_sum_leaf_weights r)
                     ,   WTree_weights_match l
                     &   WTree_weights_match r ]
  end%num.

Definition wf_Urn {A} (u : Urn A) : bool :=
  (N.pos (WTree_count (wtree u)) == getSize (size u)) &&
  WTree_weights_match (wtree u).

(******************************************************************************)

Definition WTree_insert_guarantee {A} (w' : Weight) (wt : WTree A)
                                  (wt' : WTree A) : bool :=
  [&& WTree_weights_match wt'
  &   WTree_sum_leaf_weights wt + w' == WTree_sum_leaf_weights wt']%num.
Arguments WTree_insert_guarantee {A} w' wt wt' /.

Lemma insert_WTree_wf {A} (w' : Weight) (a' : A) (u : Urn A) :
  WTree_weights_match (wtree u) ->
  WTree_insert_guarantee w' (wtree u) (wtree $ insert w' a' u).
Proof.
  move: u => [[s] wt]; cbv [insert wtree size getSize funcomp].
  set winsert := foldWTree _ _ _.
  elim/WTree_deep_rect: wt s => [w a | w l IHl r IHr] s;
    cbv [winsert foldWTree]; fold @foldWTree winsert.
  - by rewrite /= eq_refl.
  - cbv [WTree_weights_match]; fold @WTree_weights_match
      => /and3P [/eqP eq_w wm_l wm_r].
    set s' := N.div2 s; move: IHl IHr => /(_ s' wm_l) /andP [IHl_wm /eqP IHl_w]
                                         /(_ s' wm_r) /andP [IHr_wm /eqP IHr_w].
    
    by cbv [evenSize div2Size funcomp];
       case: (N.even s) => /=;
       rewrite ?IHl_wm -?IHl_w ?wm_l
               ?IHr_wm -?IHr_w ?wm_r
               eq_w
               -!N.add_assoc ?(N.add_comm w')
               !eq_refl.
Qed.

Lemma insert_WTree_count {A} (w' : Weight) (a' : A) (u : Urn A) :
  WTree_count (wtree $ insert w' a' u) == (WTree_count (wtree u) + 1)%positive.
Proof.
  move: u => [[s] wt]; cbv [insert wtree size getSize funcomp].
  set winsert := foldWTree _ _ _.
  elim/WTree_deep_rect: wt s => [w a | w l IHl r IHr] s;
    cbv [winsert foldWTree]; fold @foldWTree winsert => //=.
  by cbv [evenSize div2Size funcomp];
     case: (N.even s) => /=;
     [ move: IHl => /(_ (N.div2 s))/eqP->
     | move: IHr => /(_ (N.div2 s))/eqP-> ];
     rewrite -!Pos.add_assoc ?(Pos.add_comm 1) eq_refl.
Qed.

Theorem insert_wf {A} (w' : Weight) (a' : A) (u : Urn A) :
  wf_Urn u -> wf_Urn (insert w' a' u).
Proof.
  move=> /andP[count wm]; apply/andP; split.
  - move: (insert_WTree_count w' a' u) => /eqP->.
    move: u count {wm} => [[s] wt] /=.
    by rewrite Pos.add_1_r Npos_succ_swap => /eqP->.
  - by move: wm => /(insert_WTree_wf w' a')/andP[].
Qed.

(******************************************************************************)

Definition WTree_uninsert_guarantee_Some {A} (wt : WTree A)
                                             (w' : Weight) (wt' : WTree A) : bool :=
  [&& WTree_weights_match wt'
  &   WTree_sum_leaf_weights wt == WTree_sum_leaf_weights wt' + w']%num.
Arguments WTree_uninsert_guarantee_Some {A} wt w' wt' /.

Definition WTree_uninsert_guarantee_None {A} (wt : WTree A) (w' : Weight) : bool :=
  match wt with
    | WLeaf w _   => w == w'
    | WNode _ _ _ => false
  end.
Arguments WTree_uninsert_guarantee_None {A} wt w' /.

Definition WTree_uninsert_guarantee {A} (wt  : WTree A)
                                        (res : Weight * A * Weight * option (WTree A))
                                      : bool :=
  match res with
    | (w', _, _, Some wt') => WTree_uninsert_guarantee_Some wt w' wt'
    | (w', _, _, None)     => WTree_uninsert_guarantee_None wt w'
  end.
Arguments WTree_uninsert_guarantee {A} wt res /.

Definition uninsert_to_wuninsert {A} (res : Weight * A * Weight * option (Urn A))
                                     : Weight * A * Weight * option (WTree A) :=
  match res with
    | (w, a, lb, ou) => (w, a, lb, omap wtree ou)
  end.

Ltac foldWTree_rec name :=
  match goal with
    | |- context[foldWTree _ _ _ ?sz ?wt] =>
      rewrite /foldWTree;
      match goal with
        | |- context[?go sz wt] =>
          set name := go
      end
  end.

Lemma uninsert_WTree_wf {A} (u : Urn A) :
  WTree_weights_match (wtree u) ->
  WTree_uninsert_guarantee (wtree u) (uninsert_to_wuninsert $ uninsert u).
Proof.
  move: u => [s' wt]; cbv [uninsert wtree size funcomp].
  foldWTree_rec wuninsert.
  case unins_res: (wuninsert _ _) => [[[w' a'] lb] owt'].
  cbv [uninsert_to_wuninsert]; rewrite omap_comp'; cbv [funcomp wtree]; rewrite omap_id'.
  move: unins_res => <-; clear.
  set s := predSize' s'. (* Don't care about its value. *)
  elim/WTree_deep_rect: wt s => [w a | w l IHl r IHr] s; clear s';
    cbv [wuninsert foldWTree]; fold @foldWTree wuninsert.
  - by rewrite /= eq_refl.
  - cbv [WTree_weights_match]; fold @WTree_weights_match
      =>  /and3P [/eqP eq_w wm_l wm_r].
    set s' := div2Size s; move: IHl IHr => /(_ s' wm_l) IHl /(_ s' wm_r) IHr.
    case: (evenSize s) => /=.
    + case: (wuninsert s' l) IHl => [[[w' a'] lb] [l'|]] /=.
      * move=> /andP[-> /eqP IHl_w].
        rewrite wm_r IHl_w -!N.add_assoc ?(N.add_comm w') eq_refl !andbT.
        move: (IHl_w) =>/esym/N.add_sub_eq_r<-.
        rewrite eq_w N.add_sub_swap //= IHl_w N.add_comm.
        apply N.le_add_r.
      * rewrite wm_r andTb.
        case: l {eq_w wm_l wm_r} => [w'' [a''|//]] /eqP->/= {w'' a''}.
        by rewrite N.add_comm.
    + case: (wuninsert s' r) IHr => [[[w' a'] lb] [r'|]] /=.
      * move=> /andP[-> /eqP IHr_w].
        rewrite wm_l IHr_w -!N.add_assoc ?(N.add_comm w') eq_refl !andbT.
        move: (IHr_w) =>/esym/N.add_sub_eq_r<-.
        rewrite eq_w N.add_sub_assoc //= IHr_w N.add_comm.
        apply N.le_add_r.
      * rewrite wm_l andTb.
        by case: r {eq_w wm_l wm_r} => [w'' [a''|//]] /eqP->/= {w'' a''}.
Qed.

Lemma uninsert_WTree_count {A} (u : Urn A) :
  match uninsert u with
    | (_, _, ou') =>
      oapp (fun u' => WTree_count (wtree u') + 1) 1 ou' == WTree_count (wtree u)
  end%positive.
Proof.
  move: u => [s' wt]; cbv [uninsert wtree size getSize funcomp].
  foldWTree_rec wuninsert.
  set s := predSize' s'. (* Don't care about its value. *)
  case unins_res: (wuninsert _ _) => [[[w' a'] lb] owt'].
  rewrite oapp_omap'; cbv [funcomp].
  elim/WTree_deep_rect: wt s w' a' lb owt' unins_res => [w a | w l IHl r IHr] s w' a' lb owt';
    cbv [wuninsert foldWTree]; fold @foldWTree wuninsert => //=.
  - by move=> [] *; subst.
  - case: (evenSize s).
    + by case unins_res: (wuninsert _ _) => [[[wl al] lbl] [l'|]] [? ? ? ?];
         subst wl al lbl owt' => /=;
         move: unins_res => /IHl /= /eqP<-;
         rewrite -?Pos.add_assoc (Pos.add_comm 1).
    + by case unins_res: (wuninsert _ _) => [[[wr ar] lbr] [r'|]] [? ? ? ?];
         subst wr ar lb owt' => /=;
         move: unins_res => /IHr /= /eqP<-;
         rewrite -?Pos.add_assoc.
Qed.        

Theorem uninsert_wf {A} (u : Urn A) :
  wf_Urn u ->
  match uninsert u with
    | (_, _, _, Some u') => wf_Urn u'
    | (_, _, _, None)    => size u == MkSize 1
  end.
Proof.
  move=> /andP[count wm]; case res_unins: (uninsert u) => [[[w' a'] lb] [u'|]].
  - apply/andP; split.
    + move: (uninsert_WTree_count u); rewrite res_unins /=.
      move: u count res_unins {wm} => [[s] wt].
      rewrite {1 3}/wtree {1}/size {1}/getSize.
      move=> def_s unins_res count_next; move: count_next unins_res def_s => /eqP<-.
      rewrite /uninsert;
        case: (foldWTree _ _ _ _ _) => [[[w'' a''] lb'] [u''|]] //= [? ? ? ?];
        subst w'' a'' lb' u' => /=.
      by rewrite Pos.add_1_r => /eqP<- /=; rewrite Pos.pred_N_succ.
    + by move: wm => /uninsert_WTree_wf; rewrite res_unins /= => /andP[].
  - move: wm => /uninsert_WTree_wf; rewrite res_unins /=.
    by move: u count {res_unins} => [[s] [w [a|l r]]] //= /eqP<-.
Qed.

Corollary uninsert_tuple_wf {A} (u : Urn A)
                                (w' : Weight) (a' : A) (lb : Weight) (ou' : option (Urn A)) :
  wf_Urn u ->
  uninsert u = (w', a', lb, ou') ->
  oapp wf_Urn (size u == MkSize 1) ou'.
Proof. by move=> /uninsert_wf WF EQ; move: WF; rewrite EQ. Qed.

Corollary uninsert_Some_wf {A} (u : Urn A) (w' : Weight) (a' : A) (lb : Weight) (u' : Urn A) :
  wf_Urn u ->
  uninsert u = (w', a', lb, Some u') ->
  wf_Urn u'.
Proof. by move=> /uninsert_wf WF EQ; move: WF; rewrite EQ. Qed.

Corollary uninsert_None_wf {A} (u : Urn A) (w' : Weight) (lb : Weight) (a' : A) :
  wf_Urn u ->
  uninsert u = (w', a', lb, None) ->
  size u == MkSize 1.
Proof. by move=> /uninsert_wf WF EQ; move: WF; rewrite EQ. Qed.

(******************************************************************************)

Definition replace_guarantee {A} (wNew : Weight) (wt : WTree A)
                                 (res : Weight * A * WTree A) : bool :=
  let: (w', _, wt') := res
  in [&& WTree_weights_match wt'
     ,   w' <=? WTree_sum_leaf_weights wt
     &   WTree_sum_leaf_weights wt + wNew == WTree_sum_leaf_weights wt' + w']%num.
Arguments replace_guarantee {A} wNew wt !res /.

Theorem replace_wf {A} (wNew : Weight) (aNew : A) (i : Index) (wt : WTree A) :
  WTree_weights_match wt ->
  replace_guarantee wNew wt (replace wNew aNew wt i).
Proof.
  elim/WTree_deep_rect: wt i => [w a | w l IHl r IHr] i //=;
    first (by rewrite N.leb_refl N.add_comm /=);
    move=> /and3P [/eqP eq_w wm_l wm_r].
  case def_l: l => [wl al]; case: (i < wl); rewrite -def_l.
  - move: IHl => /(_ i wm_l).
    case res: (replace wNew aNew i l) => [[w' a'] l'] /= /and3P[wm_l' w'_le /eqP wts].
    have w'_le' : (w' <=? w)%num. {
      rewrite eq_w; apply N.leb_le; eapply N.le_trans; last by apply N.le_add_r.
      by apply N.leb_le.
    }
    rewrite wm_l' wm_r !andbT; apply/and3P; split.
    + rewrite -N.add_sub_swap; last by apply N.leb_le.
      rewrite eq_w -(N.add_comm wNew) N.add_assoc (N.add_comm wNew) wts.
      rewrite N.add_sub_swap; first by rewrite N.add_sub.
      by rewrite N.add_comm; apply N.le_add_r.
    + by rewrite -eq_w.
    + by rewrite -!N.add_assoc (N.add_comm _ wNew) (N.add_comm _ w') !N.add_assoc wts.
  - move: IHr => /(_ (i - wl)%num wm_r).
    case res: (replace wNew aNew _ r) => [[w' a'] r'] /= /and3P[wm_r' w'_le /eqP wts].
    have w'_le' : (w' <=? w)%num. {
      rewrite eq_w; apply N.leb_le; eapply N.le_trans;
        last by (rewrite N.add_comm; apply N.le_add_r).
      by apply N.leb_le.
    }
    rewrite wm_l wm_r' !andbT; apply/and3P; split.
    + rewrite -N.add_sub_swap; last by apply N.leb_le.
      by rewrite eq_w -N.add_assoc wts N.add_assoc N.add_sub.
    + by rewrite -eq_w.
    + by rewrite -!N.add_assoc wts.
Qed.

Theorem replace_count {A} (wNew : Weight) (aNew : A) (i : Weight) (wt : WTree A) :
  let: (_, _, wt') := replace wNew aNew i wt
  in WTree_count wt' == WTree_count wt.
Proof.
  elim/WTree_deep_rect: wt i => [w a | w l IHl r IHr] i //=.
  case def_l: l => [wl al]; case: (i < wl); rewrite -def_l.
  - move: IHl => /(_ i).
    by case res: (replace wNew aNew i l) => [[w' a'] l'] /= /eqP->.
  - move: IHr => /(_ (i - wl)%num).
    by case res: (replace wNew aNew _ r) => [[w' a'] r'] /= /eqP->.
Qed.

Theorem replace_wf {A} (wNew : Weight) (aNew : A) (i : Weight) (u : Urn A) :
  wf_Urn u -> let: (_,_,u') := replace wNew aNew i u in wf_Urn u'.
Proof.
  case: u => [[s] wt] /andP /= [/eqP count wm]; rewrite /replace /=.
  case result: (replace _ _ _ _) => [[w' a'] wt'].
  apply/andP; split => /=.
  - by move: (replace_count wNew aNew i wt); rewrite result /= count.
  - by move: (replace_wf wNew aNew i wm); rewrite /replace_guarantee result => /and3P[].
Qed.

Corollary replace_triple_wf {A} (wNew : Weight) (aNew : A) (i : Weight) (u : Urn A)
                                (w' : Weight) (a' : A) (u' : Urn A) :
  wf_Urn u ->
  replace wNew aNew i u = (w', a', u') ->
  wf_Urn u'.
Proof. by move=> /(replace_wf wNew aNew i) WF EQ; move: WF; rewrite EQ. Qed.

(******************************************************************************)

Theorem delete_wf {A} (i : Weight) (u : Urn A) :
  wf_Urn u ->
  match delete i u with
    | (_, _, Some u') => wf_Urn u'
    | (_, _, None)    => size u == MkSize 1
  end.
Proof.
  rewrite /delete.
  move=> /uninsert_wf; case: (uninsert u) => [[w' a'] [u'|//]].
  by move=> /(replace_wf w' a' i); case: (replace _ _ _ _) => [[w'' a''] u''].
Qed.

Corollary delete_triple_wf {A} (i : Weight) (u : Urn A)
                           (w' : Weight) (a' : A) (ou' : option (Urn A)) :
  wf_Urn u ->
  delete i u = (w', a', ou') ->
  oapp wf_Urn (size u == MkSize 1) ou'.
Proof. by move=> /(delete_wf i) WF EQ; move: WF; rewrite EQ. Qed.

Corollary delete_Some_wf {A} (i : Weight) (u : Urn A)
                         (w' : Weight) (a' : A) (u' : Urn A) :
  wf_Urn u ->
  delete i u = (w', a', Some u') ->
  wf_Urn u'.
Proof. by move=> /(delete_wf i) WF EQ; move: WF; rewrite EQ. Qed.

Corollary delete_None_wf {A} (i : Weight) (u : Urn A) (w' : Weight) (a' : A) :
  wf_Urn u ->
  delete i u = (w', a', None) ->
  size u == MkSize 1.
Proof. by move=> /(delete_wf i) WF EQ; move: WF; rewrite EQ. Qed.

(******************************************************************************)

Theorem insert_uninsert {A} w x (u : Urn A) :
  wf_Urn u ->
  uninsert (insert w x u) = (w, x, Some u).
Proof.
  case: u => -[s] wt WF;
    cbv [insert];   set winsert   := foldWTree _ _ _;
    cbv [uninsert]; set wuninsert := foldWTree _ _ _;
    cbv [wtree size getSize funcomp succSize predSize'];
    rewrite Pos.pred_N_succ Pos.pred_succ.
Abort.
