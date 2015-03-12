
(** * Stratified System F - Part I *)

Require Import Arith.
Require Import Max.
Require Import Decidable.
Require Import NPeano.
Require Import Bool.
Require Import Omega.
Require Import Psatz.
Require Import List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope bool_scope.

(** ** 1.2 Definitions *)
(** *** Question 1: Types *)

Inductive typ := 
| vart : nat -> typ (**r map a de Brujin index to a type variable. *)
| arrow : typ -> typ -> typ
| fall : nat -> typ -> typ. (**r [nat] is the kind of the type which is abstracted. *)

(** The environment is a stack of values.                                   *)
(** If a term has [v] bounded variables then they are reprensented by
    de Bruijn indices [0..v-1]. From index [v] and on, the de Bruijn indices
    represent the free variables - that must appear in the environment then -
    [v] being the top of the stack                                           *)

(** The following function shifts the free type variables
    by one within the type [t].                           *)
(** [v] is the number of bounded variables
    - ie number of lambda abstractions around [t].        *)
Fixpoint tshift (t:typ) (v:nat) : typ := 
  match t with
    | vart i   =>  vart (if le_gt_dec v i then 1 + i else i)
    | arrow t1 t2  => arrow (tshift t1 v) (tshift t2 v) 
    | fall rank sP  => fall rank (tshift sP (1 + v)) 
  end.

(** The following lemma was inspired by Vouillon also we changed
    the proof a lot. It will be useful in the next section.      *)
Lemma tshift_lemma :
  forall (T : typ) (X Y : nat),
    tshift (tshift T X) (S (X + Y)) = tshift (tshift T (X + Y)) X.
Proof.
  induction T; intros X Y.
  + unfold tshift.
    destruct (le_gt_dec (S (X + Y)));
    destruct (le_gt_dec (X + Y) n);
    destruct (le_gt_dec X n);
    destruct (le_gt_dec X (1 + n)); trivial; omega.
  + apply f_equal2 with (f := arrow); trivial.
  + simpl; apply f_equal2 with (f := fall) ; trivial.
    apply IHT with (X := S X).
Qed.

(** The following function substitutes the type variable number [v]
    by [newt] inside [t].                                             *)
(** It is assumed that [v] is removed from the environment stack
    and, as always, it is assumed that [v] does not appear in [newt]. *)
Fixpoint tsubst (t:typ) (v:nat) (newt:typ) : typ := 
  match t with
    | vart l => (**r several cases*)
      if eq_nat_dec v l then (**r That's the variable to substitue*)
        newt
      else if le_gt_dec l v then (**r That's a variable before the target variable*) 
             vart l
           else (**r That's a free variable, but we have a hole (we removed the variable)
                     so we need to garbage collect the name of this variable. *)
             vart (l-1)               
    | arrow t1 t2 => arrow (tsubst t1 v newt) (tsubst t2 v newt)
    | fall rank sp => fall rank (tsubst sp (1 + v) (tshift newt 0)) 
  end.

(** The following lemma was inspired by Vouillon also we changed
    the proof a lot. It will be useful in the next section.      *)
Lemma tsubst_lemma :
  forall (T T' : typ) (X Y : nat),
    (tshift (tsubst T X T') (X + Y)) =
    (tsubst (tshift T (S (X + Y))) X (tshift T' (X + Y))).
Proof.
  induction T; intros T' X Y.
  + unfold tshift; unfold tsubst; fold tshift; fold tsubst.
    destruct (le_gt_dec (S (X + Y)) n).
    - destruct (le_gt_dec n X); try omega.
      destruct (le_gt_dec (1 + n) X); try omega.
      destruct (eq_nat_dec X n); try omega.
      destruct (eq_nat_dec X (1 + n)); try omega.
      simpl.
      destruct (le_gt_dec (X + Y) (n - 1)); try apply f_equal; omega.
    - destruct (le_gt_dec n X);
      destruct (eq_nat_dec X n) eqn:eq; auto;
      simpl;
      apply f_equal.
      * destruct (le_gt_dec (X + Y) n); trivial.
        omega.
      * destruct (le_gt_dec (X + Y) (n - 1)); trivial.
        omega.
  + simpl; apply f_equal2 with (f := arrow); trivial.
  + simpl; apply f_equal2 with (f := fall); trivial.
    rewrite <- (plus_O_n (X+Y)) at 3.
    rewrite <- (tshift_lemma T' 0 (X + Y)).
    rewrite plus_O_n.
    apply (IHT _ (S X)).
Qed.

(** *** Question 2: Terms *)

Inductive term :=
| var : nat -> term (**r maps a de Bruijn index to a term variable. *)
| abs : typ -> term -> term (**r [typ] is the type of the term which is abstracted. *)
| app : term -> term -> term
| dept : nat -> term -> term (**r [nat] is the kind of the type which is abstracted. *)
| applt: term -> typ -> term.

(** The following function shifts the free term variables
    by one within the term [t].                           *)
(** [v] is the number of bounded variables
    - ie number of lambda abstractions around [t].        *)
Fixpoint shift (t:term) (v:nat) : term :=
  match t with
    | var i   =>  var (if le_gt_dec v i then 1 + i else i)
    | abs tp trm  => abs tp (shift trm (1 + v)) 
    | app trm1 trm2  => app (shift trm1 v) (shift trm2 v)
    | dept i trm => dept i (shift trm v) 
    | applt trm tp =>  applt (shift trm v) tp
  end.

(** The following function shifts the free type variables
    by one within the term [t].                           *)
(** [v] is the number of bounded variables
    - ie number of type abstractions around [t].          *)
Fixpoint shift_typ (t:term) (v:nat) : term :=
  match t with
    | var i   => var i
    | abs tp trm  => abs (tshift tp v) (shift_typ trm v) 
    | app trm1 trm2  => app (shift_typ trm1 v) (shift_typ trm2 v)
    | dept i trm => dept i (shift_typ trm (1 + v)) 
    | applt trm tp =>  applt (shift_typ trm v) (tshift tp v)
  end.

(** The following function substitutes the type variable number [v]
    by [newt] inside [t].                                             *)
(** It is assumed that [v] is removed from the environment stack
    and, as always, it is assumed that [v] does not appear in [newt]. *)
Fixpoint subst_typ (trm:term) (v:nat) (newt:typ) := 
  match trm with
    | var l => var l 
    | abs tp trm => abs (tsubst tp v newt) (subst_typ trm v newt)
    | app trm1 trm2 => app (subst_typ trm1 v newt) (subst_typ trm2 v newt)
    | dept i trm => dept i (subst_typ trm (1 + v) (tshift newt 0)) (**r We need to bound FTV correctly, so we shift each time we cross a forall*)
    | applt trm tp => applt (subst_typ trm v newt) (tsubst tp v newt)
  end.

(** The following function substitutes the term variable number [v]
    by [newt] inside [t].                                             *)
(** It is assumed that [v] is removed from the environment stack
    and, as always, it is assumed that [v] does not appear in [newt]. *)
Fixpoint subst (trm:term) (v:nat) (newt:term) :=
  match trm with
    | var l =>
      if eq_nat_dec l v then newt
      else if le_gt_dec l v then (**r That's a variable before the target variable*) 
             var l
           else (**r That's a free variable, but we have a hole (we removed the variable)
                     so we need to garbage collect the name of this variable. *)
             var (l-1)
    | abs tp trm => abs tp (subst trm (1 + v) (shift newt 0))
    | app trm1 trm2 => app (subst trm1 v newt) (subst trm2 v newt)
    | dept i trm => dept i (subst trm v (shift_typ newt 0)) (**r We need to shift FTV inside newt, to bound FTV correctly under new forallT *)
    | applt trm tp => applt (subst trm v newt) tp
  end.

(** *** Question 3: Environments *)

(** We use an array indexed by de Bruinj indexes - a stack -.    *)
(** It can contain two sorts of info: the type of a term variable
    or the kind of a type variable.                              *)
Inductive env :=
| empty : env
| v_typ : nat -> env -> env (**r This [nat] is a kind. *)
| v : typ -> env -> env.

(** A bit of monadic programming. It will be very useful to state
    some lemmas. (Inspired by Vouillon)                           *)
Definition map_under_option (A B : Set) (f: A -> B) (x: option A):=
  match x with 
    | Some x => Some (f x)
    | None => None
  end.

(** The following function is used to get the type of
    the term variable of index [i] in the environment [e]. *)
(** This is a partial function returning an option.        *)
Fixpoint get_typ e (i:nat) :=
  match e with
    | empty => None
    | v_typ k tl => map_under_option _ _ (fun y => tshift y 0) (get_typ tl i)                                        
    | v t tl => match i with
                  | 0 => Some t
                  | S x => get_typ tl x
                end
  end.

(** The following function is used to get the kind of
    the type variable of index [i] in the environment [e]. *)
(** This is a partial function returning an option.        *)
Fixpoint get_kind e (i:nat) :=
  match e with
    | empty => None
    | v_typ k tl => match i with
                       | 0 => Some k
                       | S x => get_kind tl x 
                     end
    | v t tl => get_kind tl i
  end.

(** *** Question 4: kinding and typing predicates *)
(** *** Question 5 : kind and type inference *)

Fixpoint wf_typ (e : env) (T : typ) {struct T} : Prop :=
  match T with
    | vart X      => get_kind e X <> None
    | arrow T1 T2 => wf_typ e T1 /\ wf_typ e T2
    | fall k T2   => wf_typ (v_typ k e) T2 
  end.

(** This lemma will be useful in the next section.
    (Inspired by Vouillon but the proof is ours.)  *)
Lemma wf_typ_env_weaken :
  forall (T : typ) (e e' : env),
    (forall (X : nat), get_kind e' X = None -> get_kind e X = None) ->
    wf_typ e T -> wf_typ e' T.
Proof.
  induction T; simpl; auto.
  + intros e e' H [H1 H2].
    split; eapply IHT1 || eapply IHT2; eauto.
  + intros e e' H HT. 
    apply IHT with (e := v_typ n e); trivial.
    induction X; trivial.
    simpl; firstorder.
Qed.

(** To each definition, we will associate an equivalent
    boolean one which will be used for inference. *)
Fixpoint wf_typ_bool (e : env) (T : typ) {struct T} : bool :=
  match T with
    | vart X      => match get_kind e X with | None => false | _ => true end
    | arrow T1 T2 => wf_typ_bool e T1 && wf_typ_bool e T2
    | fall k T2   => wf_typ_bool (v_typ k e) T2 
  end.

(** And we will prove the equivalence each time. *)
Lemma wf_typ_equiv : forall T e, wf_typ_bool e T = true <-> wf_typ e T.
Proof.
  induction T; simpl; intros e.
  + destruct (get_kind e n); intuition.
    discriminate.
  + rewrite andb_true_iff.
    intuition; try (apply IHT1); try (apply IHT2); assumption.
  + apply IHT; assumption.
Qed.

(** What it means for an environment to be well-formed. *)
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

Lemma wf_env_equiv : forall e, wf_env_bool e = true <-> wf_env e.
Proof.
  induction e; simpl.
  + intuition.
  + assumption.
  + rewrite andb_true_iff.
    intuition; apply wf_typ_equiv; assumption.
Qed.

(** Kinding predicate *)
(** After Figure 5: Stratified System F Kinding Rules *)
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
                  kinding e (fall k1 tp1) (1 + max p k1).

(** This lemma will be useful in the next section. *)
Lemma kinding_wf_typ : forall e tp k, kinding e tp k -> wf_typ e tp.
Proof.
  induction 1; simpl in *; intuition.
  rewrite H in H2.
  discriminate.
Qed.

(** Kind inference *)
(** This function computes the minimal kind for a type term. *)
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
  end.

(** One of the two main theorems for this question. *)
Theorem correctness_of_kind :
  forall tp e k, kind e tp = Some k -> kinding e tp k.
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
    apply kinded_arrow; auto.
  + specialize IHtp with (e := (v_typ n e)).
    destruct (kind (v_typ n e)) as [p | _]; try discriminate.
    inversion H as [h].
    apply kinded_fall.
    apply IHtp; reflexivity.
Qed.

(** This result was not required by the subject.
    But at first we had understood it was, so here it is. *)
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
    split; simpl; try lia.
    rewrite h2.
    reflexivity.
Qed.

(** Typing predicate *)
(** After Figure 6: Stratified System F Type-Checking Rules *)
Inductive typing : env -> term -> typ -> Prop :=
| typed_var : forall e (tp : typ) (x : nat),
                get_typ e x = Some tp ->
                wf_env e ->
                typing e (var x) tp
| typed_abs : forall e (tp1 tp2 : typ) (trm1 : term),
                typing (v tp1 e) trm1 tp2 ->
                typing e (abs tp1 trm1) (arrow tp1 tp2)
| typed_app : forall e (tp tp2 : typ) (trm1 trm2 : term),
                typing  e trm1 (arrow tp2 tp) ->
                typing e trm2 tp2 ->
                typing e (Top.app trm1 trm2) tp 
| typed_dept : forall e (kl : nat) (trm1 : term) (tp1 : typ),
                 typing (v_typ kl e) trm1 tp1 ->
                 typing e (dept kl trm1) (fall kl tp1)
| typed_applt : forall e (trm : term) (tp1 tp2 : typ) (k : nat),
                  typing e trm (fall k tp1) ->
                  kinding e tp2 k ->
                  typing e (applt trm tp2) (tsubst tp1 0 tp2).

(** This lemma will be useful in the next section. *)
Lemma typing_wf_env : forall e trm tp, typing e trm tp -> wf_env e.
Proof.
  induction 1; simpl in *; intuition.
Qed.

(** eq_typ is the boolean structural equality of types. *)
(** We now know that there are cleaner ways of doing that
    like a decidable equality. *)
Fixpoint eq_typ t1 t2 : bool :=
  match (t1 , t2) with
    | (vart x , vart y) => beq_nat x y
    | (Top.arrow t11 t12 , Top.arrow t21 t22) => andb (eq_typ t11 t21) (eq_typ t12 t22)
    | (fall k11 t12 , fall k22 t22) => andb (beq_nat k11 k22) (eq_typ t12 t22)
    | _ => false
  end.

Lemma eq_typ_equiv: forall t1 t2, eq_typ t1 t2 = true <-> t1 = t2.
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
      rewrite H2 in iht1; auto.
Qed.

(** Type inference *)
Fixpoint type (e : env) (trm : term) {struct trm} : option typ :=
  match trm with
    | var x => if wf_env_bool e then get_typ e x else None
    | abs tp1 trm1 => 
      match kind e tp1 with (**r This match is not necessary but it is an historical artefact.*)
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
  end.

(** One of the two main theorems for this question. *)
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
    apply typed_abs.
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

(** ** 1.3 Basic Metatheory *)

(** *** Lemma 1.1 (Cumulativity) *)
(** Corresponds to Lemma 3 (Level Weakening for Kinding) of the paper *)

Theorem cumulativity :
  forall e t k k', kinding e t k -> k <= k' -> kinding e t k'.
Proof.
  intros e t k k' kd; revert k'.
  induction kd; intros.
  + apply (kinded_var e X k' p); trivial.
    omega.
  + rewrite <- max_idempotent.
    apply (kinded_arrow e tp1 tp2 k' k');
    (apply IHkd1 || apply IHkd2);
    lia.
  + assert (k' = 1 + max (k'-1) k1) as eq.
    lia.
    rewrite eq.
    apply (kinded_fall e k1 tp1 (k'-1)).
    apply IHkd.
    lia.
Qed.

(** ** 1.3.1 Type substitution *)
(** *** Question 1 *)

(** [insert_kind X e e'] characterizes [e'] as being the extension of
    [e] by a kinding declaration for variable [X] *)
Inductive insert_kind : nat -> env -> env -> Prop :=
| insert_0 : forall k e,
               insert_kind 0 e (v_typ k e)
| insert_v : forall n tp e e',
               insert_kind n e e'  ->
               insert_kind n (v tp e) (v (tshift tp n) e')
| insert_S_v_typ : forall n k e e',
                     insert_kind n e e' ->
                     insert_kind (S n) (v_typ k e) (v_typ k e').

(** *** Question 2 *)

Lemma insert_kind_get_kind :
  forall n e e' l,
    insert_kind n e e' ->
    get_kind e l = get_kind e' (if le_gt_dec n l then S l else l).
Proof.
  intros; revert l.
  induction H.
  + simpl in *.
    destruct l; eauto.
  + eauto.
  + intuition. 
    destruct l; trivial.
    specialize (IHinsert_kind l).
    simpl get_kind at 1.
    rewrite IHinsert_kind.
    destruct (le_gt_dec n l); destruct (le_gt_dec (S n) (S l)); eauto; omega.
Qed.

(** Well-formedness is invariant by weakening *)
Lemma insert_kind_wf_typ :
  forall T n e e',
    insert_kind n e e' -> wf_typ e T -> wf_typ e' (tshift T n).
Proof.
  induction T;
  intros n' e e' a b; simpl in *. 
  + rewrite <- (insert_kind_get_kind n' e e' n); eauto.
  + destruct b; eauto.
  + exact (IHT (S n') (v_typ n e) _ (insert_S_v_typ _ _ _ _ a) b).
Qed.

Theorem insert_kind_wf_env :
  forall (X : nat) (e e' : env),
    insert_kind X e e' -> wf_env e -> wf_env e'.
Proof.
  induction 1; simpl; auto.
  intros [T E].
  split; try eapply insert_kind_wf_typ; eauto.
Qed.

(** Kinding is invariant by weakening *)
(** This corresponds to Lemma 8 (Context Weakening for Kinding) of the paper *)
(** We could also add the dual Lemma 10 (Context Strengthening for Kinding) *)
Theorem insert_kind_kinding :
  forall T X e e' k,
    insert_kind X e e' ->
    kinding e T k ->
    kinding e' (tshift T X) k.
Proof.
  induction T; intros X e e' k H1 H2.
  + inversion H2.
    apply kinded_var with (p := p); trivial.
    - rewrite <- H0.
      symmetry.
      apply insert_kind_get_kind.
      assumption.
    - eapply insert_kind_wf_env; eassumption.
  + simpl.
    rewrite <- max_idempotent.
    apply kinded_arrow.
    - apply IHT1 with (e := e); trivial.
      inversion H2.
      apply cumulativity with (k := p); trivial; lia.
    - apply IHT2 with (e := e); trivial.
      inversion H2.
      apply cumulativity with (k := q); trivial; lia.
  + simpl.
    inversion H2.
    apply kinded_fall.
    apply IHT with (e := v_typ n e); trivial.
    now apply insert_S_v_typ.
Qed.

(** Typing is invariant by weakening *)
Lemma insert_kind_get_typ :
  forall (X : nat) (e e' : env),
    insert_kind X e e' ->
    forall (y : nat),
      map_under_option _ _ (fun y => tshift y X) (get_typ e y) = get_typ e' y.
Proof.
  induction 1; intros y; simpl.
  + trivial.
  + induction y; trivial.
  + erewrite <- IHinsert_kind.
    destruct (get_typ e y); trivial.
    simpl.
    apply f_equal.
    exact (tshift_lemma t 0 n).
Qed.

Theorem insert_kind_typing :
  forall (e e' : env) (X : nat) (trm : term) (tp : typ),
    insert_kind X e e' ->
    typing e trm tp ->
    typing e' (shift_typ trm X) (tshift tp X).
Proof.
  intros e e' X trm tp H1 H2;
  revert e' X H1; induction H2;
  intros e' X H1; simpl.
  + apply typed_var.
    - rewrite <- insert_kind_get_typ with (X := X) (e := e); trivial.
      rewrite H.
      reflexivity.
    - eapply insert_kind_wf_env; eauto.
  + apply typed_abs.
    apply IHtyping.
    now apply insert_v.
  + eapply typed_app.
    - now eapply IHtyping1.
    - now eapply IHtyping2.
  + apply typed_dept.
    apply IHtyping.
    now apply insert_S_v_typ.
  + rewrite (tsubst_lemma _ _ 0 X).
    eapply typed_applt; eauto.
    simpl.
    eapply insert_kind_kinding; eauto.
Qed.

(** *** Question 3 *)

Inductive env_subst : nat -> typ -> env -> env -> Prop := 
| subst_Svtyp: (**r under the constructors*)
    forall e e' n k T,
      env_subst n T e e' ->
      env_subst (S n) (tshift T 0) (v_typ k e) (v_typ k e')   
| subst_SV: (**r Substitute from the end to the beginning*)
    forall e e' n T tp,
      env_subst n T e e' ->
      env_subst n T (v tp e) (v (tsubst tp n T) e')
| substv: (**r We need to substitue in [e]*)
    forall e k T,
      wf_typ e T ->
      env_subst 0 T (v_typ k e) e.

(** The subject does not clearly ask for it
    but we'll prove some weakening lemmas. *)

Lemma wf_typ_weakening_v_typ :
  forall (e : env) (T : typ) (X : nat),
    wf_typ e T -> wf_typ (v_typ X e) (tshift T 0).
Proof.
  intros.
  eapply insert_kind_wf_typ; eauto.
  apply insert_0.
Qed.

Lemma wf_typ_weak_strength_var :
  forall (e : env) (T1 T2 : typ),
    wf_typ e T2 <-> wf_typ (v T1 e) T2.
Proof.
  split; apply wf_typ_env_weaken; trivial.
Qed.

Lemma get_typ_wf :
  forall (e : env) (n : nat) (T : typ),
    wf_env e -> get_typ e n = Some T -> wf_typ e T.
Proof.
  induction e; simpl; intuition; try discriminate.
  + destruct (get_typ e n0) eqn:eq; try discriminate.
    simpl in H0.
    inversion H0.
    apply wf_typ_weakening_v_typ.
    eauto.
  + apply wf_typ_weak_strength_var.
    destruct n; eauto.
    inversion H0 as [h0]; rewrite <- h0; auto.
Qed.

(** The following lemmas are deeply inspired by Vouillon
    even if the proof is ours alone.                     *)
Lemma env_subst_get_bound_lt :
  forall (X X' : nat) (e e' : env) (T : typ),
    (env_subst X' T e e') ->
    X < X' ->
    get_kind e' X = get_kind e X.
Proof.
  intros X X' e e' T H; revert X.
  induction H; simpl; trivial; intros X H1; try omega.
  induction X; trivial.
  apply IHenv_subst.
  omega.
Qed.

Lemma env_subst_get_bound_gt :
  forall (X X' : nat) (e e' : env) (T : typ),
    env_subst X' T e e' ->
    X' < X ->
    get_kind e' (X - 1) = get_kind e X.
Proof.
  intros X X' e e' T H; revert X.
  induction H; simpl; trivial; intros X H1.
  + induction X; simpl; trivial.
    destruct (X - 0) eqn:eq; try omega.
    rewrite <- IHenv_subst; try (apply f_equal); omega.
  + induction X; try (apply f_equal); try omega.
Qed.

Lemma env_subst_wf_typ :
  forall T1 X T2 e e',
    env_subst X T2 e e' ->
    wf_env e' ->
    wf_typ e T1 ->
    wf_typ e' (tsubst T1 X T2).
Proof.
  induction T1.
  + simpl; intros.
    destruct (eq_nat_dec X n).
  - rewrite e0 in H; clear e0 X H1; revert H H0.
    induction 1; simpl; intuition.
    * now apply wf_typ_weakening_v_typ.
    * now apply wf_typ_weak_strength_var.
  - destruct (le_gt_dec n X); simpl.
    * erewrite env_subst_get_bound_lt; eauto.
      omega.
    * erewrite env_subst_get_bound_gt; eauto.
    + firstorder.
    + simpl; intros.
      eapply IHT1; eauto.
      eapply subst_Svtyp; eauto.
Qed.

Lemma typing_wf_typ : forall e u W, typing e u W -> wf_typ e W.
Proof.
  induction 1; intuition.
  + eapply get_typ_wf; eauto.
  + simpl.
    split.
  - specialize typing_wf_env with (e := v tp1 e).
    simpl.
    firstorder.
  - apply wf_typ_env_weaken with (e := v tp1 e); trivial.
    + simpl in *.
      intuition.
    + simpl in *.
      eapply env_subst_wf_typ; eauto.
  - apply substv.
    eapply kinding_wf_typ; eauto.
  - eapply typing_wf_env; eauto.
Qed.

(** Well-formedness is invariant by [env_subst] *)
(** Corresponds to part 2 of Lemma 4 (Context-Ok) of the article *)
Theorem env_subst_wf_env :
  forall X T e e',
    env_subst X T e e' ->
    wf_env e ->
    wf_env e'.
Proof.
  induction 1; firstorder.
  eapply env_subst_wf_typ; eauto.
Qed.

(** part 1 of Lemma 4 (Substitution for Kinding) of the article *)
Theorem subst_kinding :
  forall X T1 T2 k e e',
  env_subst X T1 e e' ->
  kinding e T2 k ->
  kinding e' (tsubst T2 X T1) k.
Proof.
  admit.
Qed.

(** ** 1.3.2 Term substitution *)

Fixpoint remove_var (x:nat) (e:env) {struct e} : env :=
  match e with
    | empty => empty
    | v_typ k e => v_typ k (remove_var x e)
    | v t e => match x with
                 | 0 => e
                 |S X => v t (remove_var X e)
               end
  end.

Lemma get_typ_wk :
  forall e x y, x < y -> get_typ e x = get_typ (remove_var y e) x.
Proof.
  induction e; intuition.
  + simpl in *.
    rewrite (IHe x y); trivial.
  + induction y.
    - inversion H.
    - induction x. 
      * eauto. 
      * apply IHe; omega.
Qed.

Lemma get_remove :
  forall e n x , S x > n -> get_typ (remove_var n e) x = get_typ e (S x).
Proof.
  induction e; induction n; induction x; firstorder.
  - simpl.
    rewrite <- (IHe n 0).
    reflexivity.
    omega.
  - simpl get_typ. 
    rewrite <- (IHe n (S x)).
    simpl.
    reflexivity.
    apply H.
  - omega.
Qed.

Lemma get_remove_2 :
  forall e x  n , x < n -> get_typ e  x = get_typ (remove_var n e) x .
Proof.
  induction e; trivial; intros x' n' H.
  - induction n'.
    * inversion H.
    * clear IHn'.
      induction n; simpl; trivial.
      rewrite (IHe x' (S n')); trivial; omega.
  - simpl.
    induction x'; induction n'; firstorder; omega.
Qed. 

Lemma get_kind_remove :
  forall e x x', get_kind e x = get_kind (remove_var x' e) x.
Proof.
  induction e.
  * induction x'; simpl; trivial.
  * induction x; trivial.
    intros.
    simpl in *.
    auto.
  * induction x'; intros; simpl; trivial.
Qed.

Lemma wf_typ_add : forall t e n, wf_typ (remove_var n e) t -> wf_typ e t.
Proof.
  induction t; firstorder.
  - simpl in *.
    rewrite (get_kind_remove e n n0).
    apply H.
Qed.

Theorem kinding_add:
  forall u e n  W ,
  wf_env e -> kinding (remove_var n e) u W -> kinding e u W.
Proof.
  induction u; intuition; inversion H0.
  + eapply kinded_var; eauto.
    erewrite get_kind_remove; eauto.
  + apply kinded_arrow; firstorder.
  + apply kinded_fall; firstorder.
Qed.

(** To shift the first [n] variables in [u] is the same as
    to remove the first [n] variables from [e] *)
Lemma typ_shift_remove:
  forall (e : env) (u : term) (W : typ) (n : nat),
  wf_env e -> typing (remove_var n e) u W -> typing e (shift u n) W.
Proof.
  intuition.
  assert (exists e', e'= remove_var n e) as [x H1].
  - exists (remove_var n e); trivial.
  - intros.
    rewrite <- H1 in H0.
    revert n e H1 H; induction H0; firstorder; simpl.
    * apply typed_var.
      rewrite H1 in H.
      simpl in *.
      destruct (le_gt_dec n x).
      + erewrite <- get_remove; eauto; omega.
      + erewrite get_remove_2; eauto; omega.
      + apply H2.
    * apply typed_abs.
      apply IHtyping.
      now rewrite H1.
      simpl.
      firstorder.
      specialize typing_wf_env with (e := v tp1 e) (trm := trm1) (tp := tp2); firstorder.
      apply wf_typ_add with (n := n).
      now rewrite <- H1.
    * eapply typed_app; eauto.
    * apply typed_dept.
      apply IHtyping.
      now rewrite H1.
      simpl.
      exact H.
    * eapply typed_applt; eauto.
      eapply kinding_add with (n := n); eauto.
      now rewrite <- H1.
Qed.

(** Well-formedness is invariant by [remove_var] *)
Lemma wf_typ_remove:
  forall t e n, wf_typ e t -> wf_typ (remove_var n e) t.
Proof.
  induction t; firstorder; simpl in *.
  now rewrite <- get_kind_remove.
Qed.

Theorem wf_env_remove: forall n e, wf_env e -> wf_env (remove_var n e).
Proof.
  induction n; induction e; firstorder. 
  now apply wf_typ_remove.
Qed.

(** Kinding is invariant by [remove_var]. *)
Theorem kinding_remove :
  forall tp2 e k n',
  wf_env e -> kinding e tp2 k -> kinding (remove_var n' e) tp2 k.
Proof.
  induction tp2; firstorder; inversion H0. 
  + eapply kinded_var; eauto.
    - rewrite <- H2.
      symmetry.
      apply get_kind_remove.
    - apply wf_env_remove; assumption.
  + apply kinded_arrow; firstorder.
  + apply kinded_fall; firstorder.
Qed.

(** Inspired by Vouillon. *)
Lemma typing_weakening_var :
  forall (e : env) (t : term) (U V : typ),
    wf_typ e V -> typing e t U -> typing (v V e ) (shift t 0) U.
Proof.
  intros.
  apply typ_shift_remove; trivial.
  simpl; firstorder.
  eapply typing_wf_env; eauto.
Qed.

Lemma typing_remove_vtyp:
  forall e u W kl,
  wf_typ e W ->
  typing e u W ->
  typing (v_typ kl e) (shift_typ u 0) (tshift W 0).
Proof.
  (**r The good way is to generalize slightly, saying that e' is e with et new kind somewhere*)
  intros.
  eapply insert_kind_typing; eauto.
  apply insert_0.
Qed.

Theorem subst_preserves_typing :
  forall (e : env) (x : nat) (t u : term) (V W : typ),
    typing e t V -> 
    typing (remove_var x e) u W -> get_typ e x = Some W ->
    typing (remove_var x e) (subst t x u) V.
Proof.
  intros e n t u V W H ; revert n u W; induction H; intros n' u W H1 E1; simpl.
  - destruct (eq_nat_dec x n') as [H2 | H2].
    + rewrite H2 in H; rewrite E1 in H.
      inversion H.
      now rewrite <- H4.
    + case le_gt_dec; intros H3; apply typed_var;
      try (eapply typing_wf_env; eauto).
      * rewrite <- (get_typ_wk e x n'); auto; omega.
      * rewrite get_remove; try omega.
        assert (S (x - 1) = x) as eq.
        omega.
        rewrite eq; assumption.
  - apply typed_abs.
    apply (IHtyping  (S n') (shift u 0) W); trivial.
    simpl.
    assert(wf_env (v tp1 e)).
    eapply typing_wf_env; eauto.
    simpl in H0.
    destruct H0.   
    apply typing_weakening_var; trivial.
    eapply wf_typ_remove; eauto.
  - eapply typed_app; eauto.
  - apply typed_dept.
    apply (IHtyping n' (shift_typ u 0) (tshift W 0)); simpl.
    * apply typing_remove_vtyp; firstorder.
      eapply typing_wf_typ; eauto.
    * rewrite E1; trivial.
  - eapply typed_applt; eauto.
    apply kinding_remove.
    eapply typing_wf_env; eauto.
    exact H0.
Qed.

(** The statement of the following two lemmas has been inspired by Vouillon *)
Lemma get_var_remove_var_lt :
  forall (e : env) (x x' : nat),
  x < x' -> get_typ (remove_var x' e) x = get_typ e x.
Proof.
  induction e; simpl; trivial; intros x x' H.
  + destruct x'.
    - omega.
    - rewrite IHe; trivial.
  + destruct x'; destruct x; try omega; simpl; trivial.
    apply IHe.
    omega.
Qed.

Lemma get_var_remove_var_ge :
  forall (e : env) (x x' : nat),
  x >= x' -> get_typ (remove_var x' e) x = get_typ e (1 + x).
Proof.
  induction e; simpl; trivial; intros x x' H.
  + rewrite IHe; trivial.
  + destruct x'; destruct x; try omega; simpl; trivial.
    apply IHe.
    omega.
Qed.

Theorem typing_weakening_var_ind :
  forall (e : env) (x : nat) (t : term) (U : typ),
    wf_env e -> typing (remove_var x e) t U -> typing e (shift t x) U.
Proof.
  intros e n t U H1 H2.
  assert (exists e', e' = remove_var n e) as [e' E].
  + exists (remove_var n e); trivial.
  + rewrite <- E in H2.
    revert n e E H1; induction H2; intros n' e' E H1; simpl.
    - apply typed_var; trivial.
      rewrite E in H.
      destruct le_gt_dec.
      * rewrite get_var_remove_var_ge in H; trivial; omega.
      * rewrite get_var_remove_var_lt in H; trivial; omega.
    - apply typed_abs.
      apply IHtyping.
      * rewrite E; trivial.
      * simpl.
        split; trivial.
        assert (wf_env (v tp1 e)) as H3.
        eapply typing_wf_env; eauto.
        rewrite E in H3.
        destruct H3 as [H3 _].
        eapply wf_typ_add; eauto.
    - eapply typed_app; eauto.
    - apply typed_dept.
      apply IHtyping.
      * rewrite E; trivial.
      * simpl; trivial.
    - eapply typed_applt; eauto.
      rewrite E in H.
      eapply kinding_add; eauto.
Qed.

Lemma regularity_base_case :
  forall (tp : typ) (e : env),
  wf_env e -> wf_typ e tp -> exists k : nat, kinding e tp k.
Proof.
  induction tp; intros e H0 H1; simpl in H1.
  + destruct (get_kind e n) eqn:eq; rewrite <- eq in H1; intuition.
    exists n0.
    eapply kinded_var; eauto.
  + destruct H1 as [H1tp1 H1tp2].
    destruct (IHtp1 e H0 H1tp1) as [ktp1 ihtp1].
    destruct (IHtp2 e H0 H1tp2) as [ktp2 ihtp2].
    exists (max ktp1 ktp2).
    now apply kinded_arrow.
  + assert (wf_env (v_typ n e)) as h0; firstorder.
    destruct (IHtp (v_typ n e) h0 H1) as [ihk ih].
    exists (1 + max ihk n).
    now apply kinded_fall.
Qed.

(** *** Lemma 1.2 (= Lemma 7 of paper) Regularity *)
Theorem regularity :
  forall e tp trm, typing e trm tp -> exists k, kinding e tp k.
Proof.
  induction 1.
  + revert x tp H; induction e; simpl in *; try discriminate; intros.
    - destruct (get_typ e x) eqn:eq; simpl in H; inversion H.
      destruct (IHe H0 x t eq) as [k H3].
      exists k.
      eapply insert_kind_kinding; eauto.
      apply insert_0.
    - destruct x; inversion H as [eq]; destruct H0 as [H1 H0].
      * rewrite eq in H1.
        cut (exists k, kinding e tp k).
        intros [k H2]; exists k; apply kinding_add with (n := 0); firstorder.
        now apply regularity_base_case.        
      * destruct (IHe H0 x tp eq) as [k H3].
        exists k.
        apply kinding_add with (n := 0); firstorder.
  + admit.
  + destruct IHtyping1 as [k1 ihk1].
    inversion ihk1.
    now exists q.
  + destruct IHtyping as [k1 ihk1].
    exists (1 + max k1 kl).
    now apply kinded_fall.
  + destruct IHtyping as [k1 ihk1].
    inversion ihk1.
    exists p.
    eapply subst_kinding; eauto.
    apply substv.
    eapply kinding_wf_typ; eauto.
Qed.

(** *** Lemma 1.3 Narrowing *)
(** TODO *)

(** ** 2 Reduction and Normal Terms *)
(** *** Question 1 *)

(** A relation on [term * term] is [term -> term -> Prop].           *)
(** Let's define our reduction relation with an inductive predicate. *)

(** For now we don't care about well-formedness, it will come later. *)
(** Parallel reduction.                                              *)
(** I didn't find a better, automatic way.
    Nothing about congruence relations in the lib.                   *)

Inductive oneStep : relation term :=
| redTyp : forall phi n t, oneStep (applt (dept n t) phi) (subst_typ t 0 phi) (*TO check, I think there is a mistake*)
| redTerm : forall (phi:typ) t (t':term), oneStep (Top.app (abs phi t) t') (subst t' 0  t)
| redUnderAbs : forall phi t t', oneStep t t' -> oneStep (abs phi t) (abs phi t')
| redUnderAbst : forall k t t', oneStep t t' -> oneStep (dept k t) (dept k t')
| parallelApp : forall t t' s s', oneStep t t' -> oneStep s s' -> oneStep (Top.app t s) (Top.app t' s')
| redUnderAppt : forall t t' phi, oneStep t t' -> oneStep (applt t phi) (applt t' phi)
| id : forall t, oneStep t t. (*TODO This is a choice, we could regret it later*)
(** We can do one parallelApp or two AppLeft AppRight. It's equivalent, but the second solution is easier for the proofs*)

Definition reduction (t:term) (t':term) : Prop :=
  clos_trans term oneStep t t'.

(** *** Question 2 *)

(** We could probably factorize the following proofs. *)
Lemma congruAbs :
  forall t t' phi,
  reduction t t' -> reduction (abs phi t) (abs phi t').
Proof.
  induction 1.
  - apply t_step.
    now apply redUnderAbs.
  - eapply t_trans; eauto.
Qed.

Lemma congruTypAbs :
  forall t t' k,
  reduction t t' -> reduction (dept k t) (dept k t').
Proof.
  induction 1.
  - apply t_step.
    now apply redUnderAbst.
  - eapply t_trans; eauto.
Qed.

Lemma congruTApp :
  forall t t' phi,
  reduction t t' -> reduction (applt t phi) (applt t' phi).
Proof.
  induction 1.
  - apply t_step.
    now apply redUnderAppt.
  - eapply t_trans; eauto.
Qed.

(*We split in two lemmas, then we will merge the lemmas*)
Lemma congruAppL :
  forall t t' s,
  reduction t t' -> reduction (Top.app t s) (Top.app t' s).
Proof.
  induction 1.
  - apply t_step.
    apply parallelApp; trivial.
    apply id.
  - eapply t_trans; eauto.
Qed.

Lemma congruAppR :
  forall t t' s,
  reduction t t' -> reduction (Top.app s t) (Top.app s t').
Proof.
  induction 1.
  - apply t_step.
    apply parallelApp; trivial.
    apply id.
  - eapply t_trans; eauto.
Qed.

Lemma congruApp :
  forall t t' s s',
  reduction t t' ->
  reduction s s' ->
  reduction (Top.app t s) (Top.app t' s').
Proof.
  intros.
  eapply t_trans; apply congruAppR || apply congruAppL; eauto.
Qed.

(** *** Question 3 *)

(**  System F is type erasing*)
Inductive normal : term -> Prop :=
| directlyNeutral: forall t, neutral t -> normal t
| absNorm :  forall v phi, normal v -> normal (abs phi v) 
| absTNorm : forall v k, normal v -> normal (dept k v) 
with neutral : term -> Prop := (**r A neutral term is one that is not an abstraction. *)
     | nV: forall n, neutral (var n)
     | nApplt: forall phi t, neutral t -> neutral (applt t phi)
     | nApp: forall t t', neutral t -> normal t' -> neutral (Top.app t t').

Theorem normalPreservation :
  forall t n phi,
  (normal t -> normal (subst_typ t n phi)) /\
  (neutral t -> neutral (subst_typ t n phi)). 
Proof.
  induction t; firstorder; simpl in *; inversion H; inversion H0.
  + apply absNorm; firstorder.
  + apply directlyNeutral.
    apply nApp; firstorder.
  + apply nApp; firstorder.
  + apply absTNorm; firstorder.
  + apply directlyNeutral.
    apply nApplt; firstorder.
  + apply nApplt; firstorder.
Qed.
