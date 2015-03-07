Project for the MPRI course 2.7.2.

#Advice for the report

The main purpose of this project is to **evaluate your approach to
formalization, and your comments on the value of the solutions you tried**.
Investigating several possible definitions/proof methods is a good thing and **we
value your description of the problems encountered and of the solutions you
eventually preferred** as much as the the number of questions you answer too. The
best mark will not necessarily go to the project answering the maximum number of
questions.

The report should be a separate, readable document, ideally in pdf format,
written in English or in French. It should not exceed 5 pages of a reasonably
readable document style (no magnifying glass needed). It can refer to the code
but **should explain the approach, the problems encountered, and comment the code
submitted**: is it satisfactory (data-structures, statements, proof scripts) or
were some proofs more difficult (or easier!) formally than on paper, what was
difficult and why, what ingredient or what method worked well, did you use/lack
of some automation tools...

_Now that we have spent so much time writing code, neglecting the report would
be stupid!_

#Report draft
TODO J'ai rajouté des TODO sur mes changements/
##Introduction

TODO

##Definitions

Induction on inductive predicates often comes in handy. That makes inductive
predicates a lot more powerful than functions to Prop defined with Fixpoint.

TODO : ^ POWERFULL -> 

There are other advantages to inductive predicates: for instance the ability
of just applying one of the constructs if you know that's the one that
was used. With Fixpoint definitions, you always have to consider all the
branches of the pattern matching.


We sometimes wondered why not all our functions were inductive predicates (for
instance wf_env, wf_typ) but we didn't go all the way to make the change because:

1. It was given in this way in the subject. TODO -> pas sur pour , je pense
qu'on aurait gagné du temps (it would have taken too much time.)
2. We thought that since Vouillon and the subject choose to do differently,
there might be reasons to it.

##Kind and type inference

Explain why it was difficult

The current approach of translating almost everything into boolean functions
is probably not the best one but it worked and it took us a lot of time
already so we had to move on.

TODO Afterward we realized that there was 
automatical ways to do that, but that does not change the fact that semantically,
we need to compute, so Prop is not Ok. At some point we realized that perhaps we
could put everything in Type, and not in Prop, because the special features of
Prop (erasability, impredicativy...) did not seem needed. But it did not seem
idiomatic in Coq.


##Type and term substitution

The difficulties laid:

1. In expressing correctly the theorems, especially because of De Bruijn indices;
2. In proving them because we needed tons of lemmas that the subject
nor the article provided.
TODO:
Even on paper, these lemmas were important and hard to find. We really often
wrote wrong lemmas, which led us to loose hours of sleep.
In fact, all the information we needed was in Vouillon proof scripts 
but we did not want to copy paste his things. So we started the project without 
looking at his code. But at some point, we were stuck andd then we try to look
at his code. It was the first time we read the Coq code of someone else. It
was hard to understand, with lot of unknown constructions, and a style really
different. A simple style example: in his code every proof is computed in one big
chain of tactics.
So at this point, a big part of the work was understanding and adapting (even simplifying)
a lot of lemmas and proofs from Vouillon.

Fortunately, most of the time the lemma statements need not so much semantic changes.
Because the main difference between the system we studied and the system Vouillon studied was on
the kind.

##Reduction and normal terms

This part was easier, in our opinion, than the other parts. It is probably
because, at this point we had stronger basics in Coq.

##What is hard with Coq in general

The syntax is strange and we need to know a lot of different constructions so that
we are able to move forward. There are one thousand ways to do things which are
not different but not exactly equal. 

We hadn't a clear understanding of the various automation tactics (trivial, easy,
auto, eauto, intuition, firstorder). On the contrary omega is very understandable
but it doesn't deal with max so at start we did a lot of proofs by ourselves
searching and using standard lemmas, until we found the lia tactic which deals
with max (but is sometimes buggy).

Sometimes, we would like to do proofs in a more direct style but Coq does not make
that easy. At last, we found the trick "specialize H1 with (1 := H2)" for that sort
of things.

Actually it was quite 

##Conclusion

TODO



