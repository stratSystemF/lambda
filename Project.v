Require Import Arith.

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.
Require Import Max.
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

Fixpoint wf_env (e : env) : Prop :=
  match e with
  | empty     => True
  | v T e     => wf_typ e T /\ wf_env e
  | v_typ T e => wf_env e
  end.

(* After Figure 5: Stratified System F Kinding Rules *)
Fixpoint kinding (e : env) (tp : typ) (k : nat) : Prop :=
  match tp with
  | vart X => exists p, get_kind e X = Some p /\ p <= k /\ wf_env e
  | arrow tp1 tp2 =>
      exists (p q : nat), kinding e tp1 p /\ kinding e tp2 q /\ k = max p q
  | fall k1 tp1 =>
      exists p, kinding (v_typ k1 e) tp1 p /\ k = 1 + max p k1
  end
.

(* After Figure 6: Stratified System F Type-Checking Rules *)
Fixpoint typing (e : env) (trm : term) (tp : typ) {struct trm} : Prop :=
  match trm with
  | var x => get_typ e x = Some tp /\ wf_env e
  | abs tp1 trm1 =>
      match tp with
      | arrow tp_1 tp_2 => tp_1 = tp1 /\ typing (v tp1 e) trm1 tp_2
      | _ => False
      end
  | Top.app trm1 trm2 =>
      exists (tp1 : typ), typing e trm1 (arrow tp1 tp) /\ typing e trm2 tp1
  | dept k1 trm1 =>
      match tp with
      | fall k_1 tp_1 => k1 = k_1 /\ typing (v_typ k1 e) trm1 tp_1
      | _ => False
      end
  | applt trm1 tp2 =>
      exists (tp1 : typ) (k : nat),
        tsubst tp1 0 tp2 = tp /\
        typing e trm1 (fall k tp1) /\
        kinding e tp2 k
  end
.

(*This function computes the minimal kind for a type term*)
Fixpoint kind (e : env) (tp : typ) : (option nat) :=
  match tp with
  | vart X => get_kind e X (* should also test if env if well formed *)
  | arrow tp1 tp2 => match (kind e tp1 , kind e tp2) with
                     | (Some p , Some q) => Some (max p q)
                     | _ => None
                     end
  | fall k1 tp1 => match kind (v_typ k1 e) tp1 with
                   | Some p => Some (1 + max p k1)
                   | None => None
                   end
  end
.

(* Actually this function tests for compatibility instead of equality *)
Fixpoint eq_typ t1 t2 : bool :=
  match (t1 , t2) with
  | (vart x , vart y) => true (* It's only structural, we don't care about kinds*) 
  | (arrow t11 t12 , arrow t21 t22) => andb (eq_typ t11 t21) (eq_typ t21 t22)
  | (fall k11 t12 , fall k22 t22) => andb (beq_nat k11 k22) (eq_typ t12 t22)
  | _ => false
  end
.

Fixpoint type (e : env) (trm : term) {struct trm} : option typ :=
  match trm with
  | var x => get_typ e x (* should also test if env if well formed *)
  | abs tp1 trm1 => match type (v tp1 e) trm1 with 
                      | None => None 
                      | Some tp2 => Some (arrow tp1 tp2)
                    end
  | Top.app trm1 trm2 =>
      match type e trm1 with
      | Some (arrow tp1 tp) => match type e trm2 with
                               | None => None
                               | Some tp_1 => if eq_typ tp1 tp_1 then Some tp else None
                               end
      | _ => None
      end
  | dept k1 trm1 => match type (v_typ k1 e) trm1 with 
                      | None => None 
                      | Some tp1 => Some (fall k1 tp1) 
                    end
  | applt trm1 tp2 =>
      match type e trm1 with
      | Some (fall k tp1) =>
          match kind e tp2 with
            | Some k1 => if beq_nat k1 k then Some (tsubst tp1 0 tp2) else None
            | _ => None
          end
      | _ => None
      end
  end
.

(* Remark that the wf_env condition appears here and not in the definition
 * of kind.
 *)
Theorem soundness_of_kind :
  forall tp e k, (wf_env e /\ kind e tp = Some k) -> (kinding e tp k).
Proof.
induction tp.
+ intros e k lhs.
  destruct lhs as [well_formedness H].
  unfold kinding.
  exists k.
  split.
  - rewrite <- H.
    unfold kind.
    reflexivity.
  - split.
      reflexivity.
      exact well_formedness.
+ intros e k lhs.
  destruct lhs as [well_formedness H].
  simpl in H.
  specialize IHtp1 with (e := e).
  specialize IHtp2 with (e := e).
  induction (kind e tp1) as [q1 | _].
  - induction (kind e tp2) as [q2 | _].
    * inversion H as [h].
      simpl. 
      exists q1.
      exists q2.
      split.
        apply IHtp1.
        split.
          exact well_formedness.
          reflexivity.
        split.
          apply IHtp2.
          split.
            exact well_formedness.
            split.
              reflexivity.
    * discriminate.
  - discriminate.
+ intros e k lhs.
  destruct lhs as [well_formedness H].
  simpl in H.
  specialize IHtp with (e := (v_typ n e)).
  induction (kind (v_typ n e)) as [p | _].
  - inversion H as [h].
    simpl.
    exists p.
    split.
    * apply IHtp.
      split.
        simpl.
        exact well_formedness.
        reflexivity.
    * reflexivity.
  - discriminate.
Qed.

Theorem completeness_of_kind :
 forall e tp k, (kinding e tp k) -> (forall p, p < k -> kinding e tp p -> False) -> (kind e tp = Some k).
Admitted.

Require Import GenericMinMax.

Check max_lub.
Lemma wk e tp k : (exists n,kinding (v_typ n e) tp k) -> kinding e tp k.
Proof.
admit.
Qed.

Theorem cness_of_kind :
  forall e tp k, (kinding e tp k) -> (exists p, p<=k /\ kind e tp = Some p).
Proof.
induction tp.
- intro k.
  intro kding.
  unfold kinding in kding.
  destruct kding.
  exists x.
  split.
  destruct H.
  destruct H0.
  apply H0.
  destruct H.
  rewrite <- H.
  simpl.
  reflexivity.
- intro k.
  intro kding.
  destruct kding.
  destruct H.
  destruct H as [k1 [k2 eq]].
  specialize IHtp1 with (k:=x).
  specialize IHtp2 with (k:=x0).
  assert (exists p:nat, p<= x /\ kind e tp1 = Some p).
  apply IHtp1.
  apply k1.
  assert (exists p:nat, p<= x0 /\ kind e tp2 = Some p).
  apply IHtp2.
  apply k2.
  destruct H.
  destruct H0.
  exists (max x1 x2).
  split.
  destruct H as [iequal1 k'1].
  destruct H0 as [iequal2 k'2].
  apply max_lub.
  transitivity x.
  apply iequal1.
  rewrite eq.
  apply le_max_l.
  transitivity x0.
  apply iequal2.
  rewrite eq.
  apply le_max_r.
  simpl.
  destruct H.
  destruct H0.
  rewrite H1.
  rewrite H2.
  reflexivity.
-
(*
 intro k.
  intro kding.
  simpl.
  destruct kding as [x [kd eq]].
  specialize IHtp with (k:= x).
  assert(exists p: nat, p<=x /\ kind e tp = Some p).
  apply IHtp.
  apply wk.
  exists n.
  apply kd.
  destruct H.
  destruct H.
  exists x0.
  split.
  transitivity x.
  assumption.
  transitivity (max x n).
  apply le_max_l.
  rewrite eq.
  auto.


  exists k.
  split.
  trivial.
  
.
  transitivity (max x n).
  apply le_max_l.
  auto.
  simpl.


  rewrite eq.  

  induction tp.
  * simpl. 
    destruct kd.
    
  unfold kinding in kd.
  exists k.
  split.
  reflexivity.
  simpl.    
  specialize IHtp1 with (k:=x).
  specialize IHtp2 with (k:=x0).

  destruct H2.
  destruct H3.
  destruct H2.
  destruct H3.
  rewrite H4.
  rewrite H5.
inversion H3.
  
*)



.(* No nd for now *)

Lemma weakening : forall e tp r s, kinding e tp r -> r <= s -> kinding e tp s.
Admitted.

