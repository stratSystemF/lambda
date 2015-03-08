Project for the MPRI course 2.7.2.

#Source code

[Please see the formatted source here.](http://stratSystemF.github.io/lambda)

As for the raw source file, you can find it in this repository.

#Report

##Introduction

This project has been the first contact with Coq for the two of us. We started
reading the article. We talked together to precise our understanding of the type
system and informally how to prove the different lemmas of the subject, without
any Coq considerations. Then we started to code linearly, one big file, in the
way "program what you need". Finally, we did some clean up. Usually it is not a
good way to program, but we wrote tons of
useless things, and we wanted to wait for the end of the project to be sure that
these things were actually useless.

##Definitions

We often had the choice between defining an inductive predicate or a
function into ```Prop``` with ```Fixpoint``` (for instance for the ```kinding``` and
```typing``` predicates).

When we started the project, we knew so little of Coq that we started using
```Fixpoint``` everywhere (we also did other mistakes like using ```beq_nat``` instead
of ```eq_nat_dec```). Then, by talking with other groups, we realized how much
easier some of our proofs would be if we used inductive predicates instead.
At that point, we rewrote a lot of things.

Inductive predicates have a lot of advantages:

1. There is the built-in induction construct.
2. You can just apply the right constructor rather than deconstructing
the filter construct of a ```Fixpoint``` function.

At some point, we wondered why not all our functions were inductive predicates (for
instance ```wf_env```, ```wf_typ```) but we didn't go all the way to make the change because:

1. It was given in this way in the subject and this was also the case in Vouillon's code.
2. We had a lot of proofs relying on our current construct and it was not sure that
changing everything would be an actual gain of time.

We chose to work with de Bruijn indices because it was recommended in the subject.
It was a little bit
painful, but it seems that it is because the problem is intrinsically painful. 


##Kind and type inference

We spent a lot of time on that part (way too much).
We finally managed to do it by duplicating the definition of everything
kinding and typing relied on: for each predicate, we would program an
equivalent function to booleans.

Afterward we realized that there was automatical ways to do that, but that does not change the fact that semantically,
we need to compute. So ```Prop``` is not Ok. At some point we realized that perhaps we
could put everything in ```Type```, and not in ```Prop```, because the special features of
Prop (erasability, impredicativy...) did not seem needed. But it did not seem idiomatic
in Coq to put everything in ```Type```, even when it is possible.

Thus, we are convinced that with more knowledge of Coq we would have been
able to do better on that part. But we had spent too much time on it already,
so we decide to be content with that and move on.

##Type and term substitution

The difficulties laid:

1. In expressing correctly the theorems, especially because of de Bruijn indices;
2. In proving them because we needed tons of lemmas that the subject
nor the article provided.

Even on paper, these lemmas were important and hard to find. We really often
wrote wrong lemmas, which led us to loose hours of sleep.
In fact, all the information we needed was in Vouillon proof scripts 
but we did not want to copy-paste his things. So we started the project without 
looking at his code.

At some point, we were completely stuck and then we tried to look
at his code. It was the first time we read the Coq code of someone else. It
was hard to understand, with lot of unknown constructions, and a really
different style. For instance: in his code every proof is written as one big
chain of tactics which makes it really hard to understand.

At this point, a big part of the work was to understand and to adapt
a lot of lemmas and proofs from Vouillon.

Fortunately, most of the time the lemma statements need not so much semantic changes.
Indeed, the main difference between the system we studied and the system Vouillon studied
appeared only when we dealt with kinds.


##Reduction and normal terms

This part was easier, in our opinion, than the other parts. It is probably
because, at this point we had stronger basics in Coq.

##What is hard with Coq in general

The syntax is strange and we need to know a lot of different constructions so that
we are able to move forward. There are one thousand ways to do things which are
not different but not exactly equal. 

We hadn't a clear understanding of the various automation tactics (```trivial```, ```easy```,
```auto```, ```eauto```, ```intuition```, ```firstorder```). On the contrary ```omega``` is very understandable
but it doesn't deal with ```max``` so at start we did a lot of proofs by ourselves,
searching and using standard lemmas, until we found the ```lia``` tactic which deals
with ```max``` (but is sometimes buggy).

Sometimes, we would like to do proofs in a more direct style but Coq does not make
that easy. At last, we found the trick ```specialize H1 with (1 := H2)``` for that sort
of things.

We did not find simple ways to test a proposition without actually proving it.
For example, if we have a proposition that states the equality between two things, it
would be cool to test it on small examples, to have an idea of how things works.
In this case we used the prehistorical tool named "pen".
In Haskell, it is really common to program a reference
function, an optimized function, and to use QuickCheck to test if on some random
examples it works. It seems that there is research on this subject in Coq but we
did not try what they are doing (Quikchick).

##Conclusion

Several time we had the feeling that we were playing a game, without knowing the
actual rules: the existing keywords we could use. Our learning of Coq was driven
by what we thought we needed, so we read Coq code and parts of Coq'Art, we asked strong people how to
do some stuff, we experimented blindly (and sometimes it worked and we discovered new Coq tricks).
It was kind of a chaotical experience.

There are several things which are not satisfying in our code: the style is not
uniform (we did not find our style), the code organization is not perfect, we probably missed some big
shortcuts... If we should redo the project now, it would be a lot easier, with
the basics of Coq.




 




