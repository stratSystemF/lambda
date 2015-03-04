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

##Introduction

TODO

##Definitions

Induction on inductive predicates often comes in handy. That makes inductive
predicates a lot more powerful than functions to Prop defined with Fixpoint.

There are other advantages to inductive predicates: for instance the ability
of just applying one of the constructs if you know that's was the one that
was used. With Fixpoint definitions, you always have to consider all the
branches of the pattern matching.

We sometimes wondered why not all our functions were inductive predicates (for
instance get_kind) but we didn't go all the way to make the change because:
1) It would have taken too much time.
2) We thought that since Vouillon and the subject choose to do differently,
there might be reasons to it.

##Kind and type inference

Explain why it was difficult

The current approach of translating almost everything into boolean functions
is probably not the best one but it worked and it took us a lot of time
already so we had to move on.

##Type and term substitution

The difficulties laid:
1) In expressing correctly the theorems, especially because of De Bruijn indices;
2) In proving them because we needed tons of lemmas that the subject
nor the article provided.
Even on paper, these lemmas were important and hard to find.
In fact, all the information we needed was in Vouillon proof scripts but they were
really hard to understand (almost offuscated it seemed to us).
Thus a large part of our work was understanding and adapting a lot of lemmas and
proofs from Vouillon.
Fortunately, most of the time the lemma statements needn't change.
Changes were required when the lemmas were about kinds (because this was the main
difference between the system we studied and the system Vouillon studied).

##Reduction and normal terms

TODO

##What is hard with Coq in general

The syntax is strange and we need to know a lot of different constructions so that
we are able to move forward.

We hadn't a clear understanding of the various automation tactics (trivial, easy,
auto, eauto, intuition, firstorder).

Sometimes, we would like to do proofs in a more direct style but Coq does not make
that easy. At last, we found the trick "specialize H1 with (1 := H2)" for that sort
of things.

##Conclusion

TODO



