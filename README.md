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

This project has been the first contact with Coq for the two of us. We started
reading the article. We talked together to precise our understanding of the type
system and informally how to proof the different lemmas of the subject, without
any coq considerations. Then we started to code linearly, one big file, in the
way "program what you need". Finally, we did some clean up. Usually it is not a
good way to program, but  we wrote tons of
useless things, and we wanted to wait for the end of the project to be sure that
these things were actually useless.

##Definitions

Induction on inductive predicates often comes in handy. That makes inductive
predicates a lot more handy than functions to Prop defined with Fixpoint.

There are other advantages to inductive predicates: for instance the ability
of just applying one of the constructs if you know that's the one that
was used. 

We sometimes wondered why not all our functions were inductive predicates (for
instance wf_env, wf_typ) but we didn't go all the way to make the change because:

1. It was given in this way in the subject. TODO -> pas sur pour , je pense
qu'on aurait gagné du temps (it would have taken too much time.)
2. We thought that since Vouillon and the subject choose to do differently,
there might be reasons to it.

We chose De Bruinj index because it was recommended, it was a little bit
painful, but it seems that it is because the problem is intrinsically painful. 


##Kind and type inference

The current approach of translating almost everything into boolean functions
is probably not the best one but it worked and it took us a lot of time
already so we had to move on.

Afterward we realized that there was automatical ways to do that, but that does not change the fact that semantically,
we need to compute. So Prop is not Ok. At some point we realized that perhaps we
could put everything in Type, and not in Prop, because the special features of
Prop (erasability, impredicativy...) did not seem needed. But it did not seem idiomatic
 in Coq to put everything in Type, even when it is possible.


##Type and term substitution

The difficulties laid:

1. In expressing correctly the theorems, especially because of De Bruijn indices;
2. In proving them because we needed tons of lemmas that the subject
nor the article provided.

Even on paper, these lemmas were important and hard to find. We really often
wrote wrong lemmas, which led us to loose hours of sleep.
In fact, all the information we needed was in Vouillon proof scripts 
but we did not want to copy paste his things. So we started the project without 
looking at his code. But at some point, we were stuck and then we tried to look
at his code. It was the first time we read the Coq code of someone else. It
was hard to understand, with lot of unknown constructions, and a style really
different. A simple style example: in his code every proof is computed in one big
chain of tactics (and so, by this reading we discover the chaining rules for
tactics).
At this point, a big part of the work was to understand and to adapt
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

We did not find simple way to test a proposition without actually proving it.
For example, if we have a proposition that states the equality between two things, it
could be cool to test for small examples, to have an idea of how things works.
In this case we used the prehistorical tool named "pen".
In Haskell, it is really common to program a reference
function, an optimized function, and to use QuickCheck to test if on some random
examples it works. It seems that there is research on this subject in Coq but we
did not try what they are doing (Quikchick).

##Conclusion

Severals time we had the feeling that we were playing a game, without knowing the
actual rules: the existing keywords we could use. Our learning of Coq was driven
by what we thought we need, so we read Coq code and parts of the Coq'Art, we asked strong people how to
do some stuff, we tried other stuffs. It was a kind of chaotical experience.

There are several things which are not satisfying in our code : the style is not
uniform (we did not find our style), the lemmas are chaotically organized (but
that will probably change before the presentation), we probably missed some big
shortcuts... If we should redo the project now, it would be a lot easier, with
the basics of Coqs.




 




