 Require Import Arith.

Require Import Le.
Require Import Lt.
Require Import Gt.
Require Import Decidable.

Local Open Scope nat_scope.

Inductive typ := 
  | var : nat -> typ
  | arrow : typ -> typ -> typ
  | fall : nat -> typ -> typ.
(*  Rank, secondePart*)

(* Idea : de Bruinj indexes to carry bounded variables
and free variables. So we talk globally of a first freevariabe,
a second nne and so on... *)



(*The following function shift the Free variables by one*)
Fixpoint shift (t:typ) (v:nat) : typ := 
   match t with
       | var i   =>  var (if le_gt_dec v i then 1 + i else i  )
       | arrow t1 t2  => arrow (shift t1 v) (shift t2 v) 
       | fall rank sP  => fall rank (shift sP (v+1)) 
   end.

(*I have to write an example about that*)
Fixpoint tsubst (t:typ) (v:nat) (newt :typ) := 
  match t with
      | var l => (*several cases*)
        if beq_nat v l then
          newt (*That's the variable to substitue*)
        else var l 
          (*The following comments delimit a possible optimization : the compression
of the namespace if we assume that's v is not in newt.*)
 
          (*if le_gt_dec l v (*That's a variable before the target variable*) 
             then
               var l
             else (*That's a free variable, but we have a hole (we removed the variable) so we
                   need to garbage collect the name of this variable*)
               var (l-1)
               *)
               
      | arrow t1 t2 => arrow (tsubst t1 v newt) (tsubst t2 v newt)
      | fall rank sp => fall rank (tsubst sp (v+1) (shift newt 0)) 
                             
   end.
 

Inductive term :=
  | vart : nat -> term
  | abst : typ -> term -> term
  | app : term -> term -> term
  | dept : nat -> term -> term
  | applt: term -> typ -> term.


Fixpoint shiftTrmInTrm (t:term) (v:nat) : term :=
   match t with
       | vart i   =>  vart (if le_gt_dec v i then 1 + i else i  )
       | abst tp trm  => abst tp (shiftTrmInTrm trm (v+1)) 
       | app trm1 trm2  => app (shiftTrmInTrm trm1 v) (shiftTrmInTrm trm2 v)
       | dept i trm => dept i (shiftTrmInTrm trm v) 
       | applt trm tp =>  applt (shiftTrmInTrm trm v) tp
   end.

Fixpoint shiftTpInTrm (t:term) (v:nat) : term :=
   match t with
       | vart i   =>  vart (if le_gt_dec v i then 1 + i else i  )
       | abst tp trm  => abst tp (shiftTpInTrm trm v) 
       | app trm1 trm2  => app (shiftTpInTrm trm1 v) (shiftTpInTrm trm2 v)
       | dept i trm => dept i (shiftTpInTrm trm (v+1)) 
       | applt trm tp =>  applt (shiftTpInTrm trm v) tp
   end.

Fixpoint substTypInTerm (trm:term) (v:nat) (newt :typ) := 
  match trm with
      | vart l => vart l 
      | abst tp trm => abst (tsubst tp v newt) (substTypInTerm trm v newt)
      | app trm1 trm2 => app (substTypInTerm trm1 v newt) (substTypInTerm trm2 v newt)
      | dept i trm => dept i (substTypInTerm trm (v+1) (shift newt 0))
(*We need to bound FTV correctly, so we shift each time we cross a forall*)
      | applt trm tp => applt (substTypInTerm trm v newt) (tsubst tp v newt)
   end.



Fixpoint substTermInTerm (trm:term) (v:nat) (newt : term) :=
  match trm with
    | vart l => if beq_nat l v then newt
                 else vart l
    | abst tp trm => abst tp (substTermInTerm trm (v+1) (shiftTrmInTrm newt 0))
    | app trm1 trm2 => app (substTermInTerm trm1 v newt) (substTermInTerm trm2 v newt)
    | dept i trm => dept i (substTermInTerm trm v (shiftTpInTrm newt 0))
    (* We need to shift FTV inside newt, to bound FTV correctly under new forallT *)
    | applt trm tp => applt (substTermInTerm trm v newt) tp
  end.


