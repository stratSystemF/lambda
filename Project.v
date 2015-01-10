Require Import Arith.

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.

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
      | fall rank sp => fall rank (tsubst sp (v+1) (tshift newt 0)) 
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

Fixpoint shift_typ (t:term) (v:nat) : term :=
   match t with
       | var i   =>  var (if le_gt_dec v i then 1 + i else i  )
       | abs tp trm  => abs tp (shift_typ trm v) 
       | app trm1 trm2  => app (shift_typ trm1 v) (shift_typ trm2 v)
       | dept i trm => dept i (shift_typ trm (v+1)) 
       | applt trm tp =>  applt (shift_typ trm v) tp
   end.

Fixpoint subst_typ (trm:term) (v:nat) (newt :typ) := 
  match trm with
      | var l => var l 
      | abs tp trm => abs (tsubst tp v newt) (subst_typ trm v newt)
      | app trm1 trm2 => app (subst_typ trm1 v newt) (subst_typ trm2 v newt)
      | dept i trm => dept i (subst_typ trm (v+1) (tshift newt 0))
(*We need to bound FTV correctly, so we shift each time we cross a forall*)
      | applt trm tp => applt (subst_typ trm v newt) (tsubst tp v newt)
   end.



Fixpoint subst (trm:term) (v:nat) (newt : term) :=
  match trm with
    | var l => if beq_nat l v then newt
                 else var l
    | abs tp trm => abs tp (subst trm (v+1) (shift newt 0))
    | app trm1 trm2 => app (subst trm1 v newt) (subst trm2 v newt)
    | dept i trm => dept i (subst trm v (shift_typ newt 0))
    (* We need to shift FTV inside newt, to bound FTV correctly under new forallT *)
    | applt trm tp => applt (subst trm v newt) tp
  end.

Require Import List.
Import ListNotations.


(*We use an array indexed by de Bruinj indexes*)

Inductive env :=
  | empty : env
  | v_typ : nat -> env -> env
  | v : typ -> env -> env.

Fixpoint get_typ e (i:nat) :=
  match e with
      | empty => None
      | v_typ k tl => get_typ tl i
      | v t tl => match i with
                      | 0 => Some t
                      | S x => get_typ tl x
                  end
  end.

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
  |  empty      => True
  | v T e   => wf_typ e T /\ wf_env e
  | v_typ T e => wf_env e
  end.

                                      
                   