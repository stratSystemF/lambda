 Require Import Arith.

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.

Local Open Scope nat_scope.

Inductive typ := 
  | vart : nat -> typ
  | arrow : typ -> typ -> typ
  | fall : nat -> typ -> typ.
       (* Rank -> term*)

(* Idea : de Bruinj indexes to carry bounded variables
and free variables. So we talk globally of a first freevariabe,
a second nne and so on... *)



(*The following function shift the Free variables by one*)
Fixpoint tshift (t:typ) (v:nat) : typ := 
   match t with
       | vart i   =>  vart (if le_gt_dec v i then 1 + i else i  )
       | arrow t1 t2  => arrow (tshift t1 v) (tshift t2 v) 
       | fall rank sP  => fall rank (tshift sP (v+1)) 
   end.

(*I have to write an example about that*)
Fixpoint tsubst (t:typ) (v:nat) (newt :typ) := 
  match t with
      | vart l => (*several cases*)
        if beq_nat v l then
          newt (*That's the variable to substitue*)
        else vart l 
          (*The following comments delimit a possible optimization : the compression
of the namespace if we assume that's v is not in newt.*)
 
          (*if le_gt_dec l v (*That's a variable before the target variable*) 
             then
               vart l
             else (*That's a free variable, but we have a hole (we removed the variable) so we
                   need to garbage collect the name of this variable*)
               vart (l-1)
               *)
               
      | arrow t1 t2 => arrow (tsubst t1 v newt) (tsubst t2 v newt)
      | fall rank sp => fall rank (tsubst sp (v+1) (tshift newt 0)) 
                             
   end.
 

Inductive term :=
  | var : nat -> term
  | abst : typ -> term -> term
  | app : term -> term -> term
  | dept : nat -> term -> term
  | applt: term -> typ -> term.


Fixpoint shift (t:term) (v:nat) : term :=
   match t with
       | var i   =>  var (if le_gt_dec v i then 1 + i else i  )
       | abst tp trm  => abst tp (shift trm (v+1)) 
       | app trm1 trm2  => app (shift trm1 v) (shift trm2 v)
       | dept i trm => dept i (shift trm v) 
       | applt trm tp =>  applt (shift trm v) tp
   end.

Fixpoint shift_typ (t:term) (v:nat) : term :=
   match t with
       | var i   =>  var (if le_gt_dec v i then 1 + i else i  )
       | abst tp trm  => abst tp (shift_typ trm v) 
       | app trm1 trm2  => app (shift_typ trm1 v) (shift_typ trm2 v)
       | dept i trm => dept i (shift_typ trm (v+1)) 
       | applt trm tp =>  applt (shift_typ trm v) tp
   end.

Fixpoint subst_typ (trm:term) (v:nat) (newt :typ) := 
  match trm with
      | var l => var l 
      | abst tp trm => abst (tsubst tp v newt) (subst_typ trm v newt)
      | app trm1 trm2 => app (subst_typ trm1 v newt) (subst_typ trm2 v newt)
      | dept i trm => dept i (subst_typ trm (v+1) (tshift newt 0))
(*We need to bound FTV correctly, so we shift each time we cross a forall*)
      | applt trm tp => applt (subst_typ trm v newt) (tsubst tp v newt)
   end.



Fixpoint subst (trm:term) (v:nat) (newt : term) :=
  match trm with
    | var l => if beq_nat l v then newt
                 else var l
    | abst tp trm => abst tp (subst trm (v+1) (shift newt 0))
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

                                      
                   