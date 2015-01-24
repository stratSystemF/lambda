Require Import Arith.

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.
Require Import Max.
Require Import NPeano.
Require Import GenericMinMax.
Require Import Bool.
Require Import Omega.
Local Open Scope nat_scope.

Inductive typ := 
| vart : nat -> typ
(* The latter nat is the de Brujin index of the type variable. *)
| arrow : typ -> typ -> typ
| fall : nat -> typ -> typ.
(* The latter nat is the kind of the type which is abstracted. *)

(* The environment is a stack of values *
 * If a term has v bounded variables then they are reprensented by
 * de Brujin indexes 0..v-1. From index v and on, the de Brujin indexes
 * represent the free variables - that must appear in the environment then -
 * v being the top of the stack
 *)

(* The following function shifts the free type variables by one within the type t.
 * v is the number of bounded variables - ie number of type abstractions - in t.
 *)
Fixpoint tshift (t:typ) (v:nat) : typ := 
   match t with
   | vart i   =>  vart (if le_gt_dec v i then 1 + i else i  )
   | arrow t1 t2  => arrow (tshift t1 v) (tshift t2 v) 
   | fall rank sP  => fall rank (tshift sP (1 + v)) 
   end.

(*I have to write an example about that*)
(* The following function substitutes the type variable number v by newt inside t.
 * It is assumed that v is removed from the environment stack
 * and, as always, it is assumed that v does not appear in newt.
 *)
Fixpoint tsubst (t:typ) (v:nat) (newt:typ) : typ := 
  match t with
  | vart l => (*several cases*)
    if beq_nat v l then
      newt (*That's the variable to substitue*)
    else if le_gt_dec l v then (*That's a variable before the target variable*) 
      vart l
    else (* That's a free variable, but we have a hole (we removed the variable)
          * so we need to garbage collect the name of this variable. *)
      vart (l-1)               
  | arrow t1 t2 => arrow (tsubst t1 v newt) (tsubst t2 v newt)
  | fall rank sp => fall rank (tsubst sp (1 + v) (tshift newt 0)) 
  end.


Inductive term :=
| var : nat -> term
(* The latter nat is the de Brujin index of the term variable. *)
| abs : typ -> term -> term
(* The latter typ is the type of the term which is abstracted. *)
| app : term -> term -> term
| dept : nat -> term -> term
(* The latter nat is the kind of the type which is abstracted. *)
| applt: term -> typ -> term.

(* The following function shifts the free term variables by one within the term t.
 * v is the number of bounded variables - ie number of lambda abstractions - in t.
 *)
Fixpoint shift (t:term) (v:nat) : term :=
   match t with
   | var i   =>  var (if le_gt_dec v i then 1 + i else i  )
   | abs tp trm  => abs tp (shift trm (1 + v)) 
   | app trm1 trm2  => app (shift trm1 v) (shift trm2 v)
   | dept i trm => dept i (shift trm v) 
   | applt trm tp =>  applt (shift trm v) tp
   end.

(* The following function shifts the free type variables by one within the term t.
 * v is the number of bounded variables - ie number of type abstractions - in t.
 *)
Fixpoint shift_typ (t:term) (v:nat) : term :=
   match t with
   | var i   =>  var (if le_gt_dec v i then 1 + i else i  )
   | abs tp trm  => abs tp (shift_typ trm v) 
   | app trm1 trm2  => app (shift_typ trm1 v) (shift_typ trm2 v)
   | dept i trm => dept i (shift_typ trm (1 + v)) 
   | applt trm tp =>  applt (shift_typ trm v) tp
   end.

(* The following function substitutes the type variable number v by newt inside t.
 * It is assumed that v is removed from the environment stack
 * and, as always, it is assumed that v does not appear in newt.
 *)
Fixpoint subst_typ (trm:term) (v:nat) (newt:typ) := 
  match trm with
  | var l => var l 
  | abs tp trm => abs (tsubst tp v newt) (subst_typ trm v newt)
  | app trm1 trm2 => app (subst_typ trm1 v newt) (subst_typ trm2 v newt)
  | dept i trm => dept i (subst_typ trm (1 + v) (tshift newt 0))
  (*We need to bound FTV correctly, so we shift each time we cross a forall*)
  | applt trm tp => applt (subst_typ trm v newt) (tsubst tp v newt)
  end.

(* The following function substitutes the term variable number v by newt inside t.
 * It is assumed that v is removed from the environment stack
 * and, as always, it is assumed that v does not appear in newt.
 *)
Fixpoint subst (trm:term) (v:nat) (newt:term) :=
  match trm with
  | var l =>
    if beq_nat l v then newt
    else if le_gt_dec l v then (*That's a variable before the target variable*) 
      var l
    else (* That's a free variable, but we have a hole (we removed the variable)
          * so we need to garbage collect the name of this variable. *)
      var (l-1)
  | abs tp trm => abs tp (subst trm (1 + v) (shift newt 0))
  | app trm1 trm2 => app (subst trm1 v newt) (subst trm2 v newt)
  | dept i trm => dept i (subst trm v (shift_typ newt 0))
  (* We need to shift FTV inside newt, to bound FTV correctly under new forallT *)
  | applt trm tp => applt (subst trm v newt) tp
  end.

(* Environments *)
Require Import List.
Import ListNotations.

(* We use an array indexed by de Bruinj indexes - a stack -
 * It can contain two sorts of info: the type of a term variable
 * or the kind of a type variable
 *)

Inductive env :=
| empty : env
| v_typ : nat -> env -> env
(* The latter nat is a kind. *)
| v : typ -> env -> env.

(* The following function is used to get the type of the term variable
 * of index i in the environment e.
 *)
Fixpoint get_typ e (i:nat) :=
  match e with
    | empty => None               
    | v_typ k tl => get_typ tl i
    | v t tl => match i with
                  | 0 => Some t
                  | S x => get_typ tl x
                end
  end.

(* The following function is used to get the kind of the type variable
 * of index i in the environment e.
 *)
Fixpoint get_kind e (i:nat) :=
  match e with
    | empty => None
    | v_typ k tl => match i with
                      | 0 => Some k
                      | S x => get_kind tl x 
                    end

    | v t tl => get_kind tl i
  end.

(*Comes from subject*)
Fixpoint wf_typ (e : env) (T : typ) {struct T} : Prop :=
  match T with
    | vart X      => get_kind e X <> None
    | arrow T1 T2 => wf_typ e T1 /\ wf_typ e T2
    | fall k T2   => wf_typ (v_typ k e) T2 
  end.


Local Open Scope bool_scope.

Fixpoint wf_typ_bool (e : env) (T : typ) {struct T} : bool :=
  match T with
    | vart X      => match get_kind e X with | None => false | _ => true end
    | arrow T1 T2 => wf_typ_bool e T1 && wf_typ_bool e T2
    | fall k T2   => wf_typ_bool (v_typ k e) T2 
  end
.

Theorem wf_typ_equiv : forall T e, wf_typ_bool e T = true <-> wf_typ e T.
Proof.
  induction T; simpl; intros e.
  + destruct (get_kind e n); intuition.
    discriminate.
  + rewrite andb_true_iff.
    intuition; try (apply IHT1); try (apply IHT2); assumption.
  + apply IHT; assumption.
Qed.

Fixpoint wf_env (e : env) : Prop :=
  match e with
    | empty     => True
    | v T e     => wf_typ e T /\ wf_env e
    | v_typ T e => wf_env e
  end.

Fixpoint wf_env_bool (e : env) : bool :=
  match e with
    | empty     => true
    | v T e     => andb (wf_typ_bool e T) (wf_env_bool e)
    | v_typ T e => wf_env_bool e
  end.

Theorem wf_env_equiv : forall e, wf_env_bool e = true <-> wf_env e.
Proof.
  induction e; simpl.
  + intuition.
  + assumption.
  + rewrite andb_true_iff.
    intuition; apply wf_typ_equiv; assumption.
Qed.

(* After Figure 5: Stratified System F Kinding Rules *)
Inductive kinding (e : env) : typ -> nat -> Prop :=
| kinded_var : forall X k p,
                 get_kind e X = Some p ->
                 p <= k ->
                 wf_env e ->
                 kinding e (vart X) k
| kinded_arrow : forall tp1 tp2 p q,
                   kinding e tp1 p ->
                   kinding e tp2 q ->
                   kinding e (arrow tp1 tp2) (max p q)
| kinded_fall : forall k1 tp1 p,
                  kinding (v_typ k1 e) tp1 p ->
                  kinding e (fall k1 tp1) (1 + max p k1)
.

(* This function computes the minimal kind for a type term *)
Fixpoint kind (e : env) (tp : typ) : (option nat) :=
  match tp with
    | vart X => if wf_env_bool e then get_kind e X else None
    | Top.arrow tp1 tp2 => match (kind e tp1, kind e tp2 ) with
                             | (Some p , Some q) => Some (max p q)
                             | _ => None
                           end
    | fall k1 tp1 => match kind (v_typ k1 e) tp1  with
                       | Some p => Some (1 + max p k1)
                       | None => None
                     end
  end
.

Theorem correctness_of_kind : forall tp e k, kind e tp = Some k -> kinding e tp k.
Proof.
  induction tp; intros e k H; simpl in H.
  + apply kinded_var with (p := k).
  - destruct (wf_env_bool e); trivial.
    discriminate.
  - destruct (wf_env_bool e); trivial.
  - apply wf_env_equiv.
    destruct (wf_env_bool e); trivial.
    discriminate.
    + specialize IHtp1 with (e := e).
      specialize IHtp2 with (e := e).
      destruct (kind e tp1) as [q1 | _]; try discriminate.
      destruct (kind e tp2) as [q2 | _]; try discriminate.
      inversion H as [h].
      apply kinded_arrow.
  - apply IHtp1; reflexivity.
  - apply IHtp2; reflexivity.
    + specialize IHtp with (e := (v_typ n e)).
      destruct (kind (v_typ n e)) as [p | _]; try discriminate.
      inversion H as [h].
      apply kinded_fall.
      apply IHtp; reflexivity.
Qed.

Theorem completeness_of_kind :
  forall tp e k, (kinding e tp k) -> (exists p, p<=k /\ kind e tp = Some p).
Proof.
  induction tp; intros e k kding; inversion kding.
  + exists p.
           intuition.
           rewrite <- H.
           simpl.
           rewrite <- wf_env_equiv in H2.
           rewrite H2.
           rewrite H.
           assumption.
           + intuition.
             simpl.
             specialize IHtp1 with (e := e) (k := p).
             specialize IHtp2 with (e := e) (k := q).
             destruct (IHtp1 H1) as [p0 [h1 h2]].
             destruct (IHtp2 H3) as [q0 [h3 h4]].
             exists (max p0 q0).
             split.
           - apply Nat.max_le_compat; assumption.
           - rewrite h2; rewrite h4; reflexivity.
             + specialize IHtp with (e := (v_typ n e)) (k := p).
               destruct (IHtp H2) as [p0 [h1 h2]].
               exists (1 + max p0 n). 
               split.
               * simpl.
                 apply le_n_S.
                 apply Nat.max_le_compat_r.
                 assumption.
               * simpl.
                 rewrite h2.
                 reflexivity.
Qed. 

(* After Figure 6: Stratified System F Type-Checking Rules *)
Inductive typing (e : env) : term -> typ -> Prop :=
| typed_var : forall (tp : typ) (x : nat),
                get_typ e x = Some tp ->
                wf_env e ->
                typing e (var x) tp
| typed_abs : forall (tp1 tp2 : typ) (trm1 : term),
                typing (v tp1 e) trm1 tp2 ->
                typing e (abs tp1 trm1) (arrow tp1 tp2)
| typed_app : forall (tp tp2 : typ) (trm1 trm2 : term),
                typing e trm1 (arrow tp2 tp) ->
                typing e trm2 tp2 ->
                typing e (Top.app trm1 trm2) tp 
| typed_dept : forall (kl : nat) (trm1 : term) (tp1 : typ),
                 typing (v_typ kl e) trm1 tp1 ->
                 typing e (dept kl trm1) (fall kl tp1)
| typed_applt : forall (trm : term) (tp1 tp2 : typ) (k : nat),
                  typing e trm (fall k tp1) ->
                  kinding e tp2 k ->
                  typing e (applt trm tp2) (tsubst tp1 0 tp2)
.

(* eq_typ is the decidable equality of types
   this is a strict inductive equality *)
Fixpoint eq_typ t1 t2 : bool :=
  match (t1 , t2) with
    | (vart x , vart y) => beq_nat x y
    | (Top.arrow t11 t12 , Top.arrow t21 t22) => andb (eq_typ t11 t21) (eq_typ t12 t22)
    | (fall k11 t12 , fall k22 t22) => andb (beq_nat k11 k22) (eq_typ t12 t22)
    | _ => false
  end
.

Theorem eq_typ_equiv: forall t1 t2, eq_typ t1 t2 = true <-> t1 = t2.
Proof.
  induction t1; split; destruct t2; simpl; intro H; try discriminate.
  + rewrite beq_nat_eq with (x := n) (y := n0); intuition.
  + inversion H.
    symmetry.
    apply beq_nat_refl.
  + apply andb_true_iff in H; destruct H as [H1 H2].
    specialize IHt1_1 with (t2 := t2_1); destruct IHt1_1 as [iht1 _].
    specialize IHt1_2 with (t2 := t2_2); destruct IHt1_2 as [iht2 _].
    rewrite (iht1 H1).
    rewrite (iht2 H2).
    reflexivity.
  + inversion H.
    apply andb_true_iff; split.
  - specialize IHt1_1 with (t2 := t2_1); destruct IHt1_1 as [_ iht1].
    pattern t2_1 at 1; rewrite <- H1.
    intuition.
  - specialize IHt1_2 with (t2 := t2_2); destruct IHt1_2 as [_ iht2].
    pattern t2_2 at 1; rewrite <- H2.
    intuition.
    + apply andb_true_iff in H; destruct H as [H1 H2].
      specialize IHt1 with (t2 := t2); destruct IHt1 as [iht1 _].
      rewrite (iht1 H2).
      rewrite beq_nat_eq with (x := n) (y := n0); intuition.
    + inversion H.
      apply andb_true_iff; split.
  - symmetry; apply beq_nat_refl.
  - specialize IHt1 with (t2 := t2); destruct IHt1 as [_ iht1].
    rewrite H2 in iht1.
    apply iht1.
    reflexivity.
Qed.

Fixpoint type (e : env) (trm : term) {struct trm} : option typ :=
  match trm with
    | var x => if wf_env_bool e then get_typ e x else None
    | abs tp1 trm1 => 
      match kind e tp1 with (*This match is not necessary but it is an historical artefact.*)
        | Some a =>
          match type (v tp1 e) trm1  with 
            | None => None 
            | Some tp2 => Some (Top.arrow tp1 tp2)
          end
        | None => None
      end
    | Top.app trm1 trm2 =>
      match type e trm1  with
        | Some (Top.arrow tp1 tp) =>
          match type e trm2 with
            | None => None
            | Some tp_1 => if eq_typ tp1 tp_1 then Some tp else None
          end
        | _ => None
      end
    | dept k1 trm1 =>
      match type (v_typ k1 e) trm1  with 
        | None => None 
        | Some tp1 => Some (fall k1 tp1) 
      end
    | applt trm1 tp2 =>
      match type e trm1  with
        | Some (fall k tp1) =>
          match kind e tp2  with
            | Some k1 => if beq_nat k1 k then Some (tsubst tp1 0 tp2) else None
            | _ => None
          end
        | _ => None
      end
  end
.

Theorem correctness_of_type :
  forall trm tp e, type e trm = Some tp -> typing e trm tp.
Proof.
  induction trm; intros tp e typ; simpl in typ.
  + apply (typed_var). 
  - destruct (wf_env_bool e); trivial.
    discriminate.
  - apply wf_env_equiv.
    destruct (wf_env_bool e); trivial.
    discriminate.
    + destruct (kind e t) eqn:eq1; try discriminate.
      destruct (type (v t e) trm) eqn:eq; try discriminate.
      inversion typ.
      apply (typed_abs).
      apply IHtrm; assumption.
    + destruct (type e trm1) eqn:eq; try discriminate.
      destruct (t) eqn:eq2; try discriminate.
      destruct (type e trm2) eqn:eq1; try discriminate.
      apply (typed_app e tp t0_1 trm1 trm2).
  - apply (IHtrm1).
    rewrite eq.
    destruct (eq_typ t0_1 t0) eqn:eq3; try discriminate.
    inversion typ.
    reflexivity.
  - apply (IHtrm2).
    destruct (eq_typ t0_1 t0) eqn:eq3; try discriminate.
    rewrite eq1.
    induction t0.
    * specialize eq_typ_equiv with (t1 := t0_1) (t2 := vart n).
      intros H; destruct H as [H1 H2].
      rewrite H1; intuition.
    * apply eq_typ_equiv in eq3.
      rewrite eq3; reflexivity.
    * apply eq_typ_equiv in eq3.
      rewrite eq3; reflexivity.
    + destruct (type (v_typ n e) trm) eqn:eq; try discriminate.
      destruct tp; try discriminate.
      inversion typ.
      rewrite <- H0.
      apply (typed_dept e n trm tp).
      apply IHtrm. 
      rewrite <- H1.
      assumption.
    + destruct (type e trm) eqn:eq; try discriminate.
      destruct t0; try discriminate.
      destruct (kind e t) eqn:eq1; try discriminate.
      destruct (beq_nat n0 n) eqn:eq2; try discriminate.
      inversion typ.
      apply (typed_applt e trm t0 t n).
  - apply IHtrm.
    assumption.
  - apply correctness_of_kind.
    rewrite eq1.
    rewrite beq_nat_eq with (x := n0) (y := n); intuition.
Qed.

(* insert_kind X e e' characterizes e' as being the extension of e by a
 * kinding declaration for variable X *)
Inductive insert_kind : nat -> env -> env -> Prop :=
| insert_0 : forall k e,
                   insert_kind 0 e (v_typ k e)
| insert_S_v : forall n tp e e',
               insert_kind (S n) e e' ->
               insert_kind (S n) (v tp e) (v (tshift tp n) e')
| insert_S_v_typ : forall n k e e',
                   insert_kind n e e' ->
                   insert_kind (S n) e (v_typ k e')
.

Lemma wf_env_typ : forall e tp, wf_env (v tp e) -> wf_typ e tp.
Proof.
intros e tp H.
simpl in H.
easy.
Qed.
(*
Lemma insert_kind_wf_typ : forall (X : nat) (e e' : env) (tp : typ),
                             insert_kind X e e' ->
                             wf_env e ->
                             wf_env (v (tshift tp X) e').
Proof.
*)
Lemma insert_kind_wf_env : forall (X : nat) (e e' : env),
                             insert_kind X e e' -> wf_env e -> wf_env e'.
induction X; intros e e' H wfness.
+ inversion H.
  easy.
+ destruct e'; inversion H; simpl.
  - now apply (IHX e).
  - split.
    * apply wf_env_typ.
      apply insert_kind_wf_env.