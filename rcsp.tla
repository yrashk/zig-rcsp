-------------- MODULE rcsp -----------------------

(*

This specification is an attempt to model the behaviour of code in zig-rcsp (Reference-counted Shared Pointer)

*)

EXTENDS TLC, Integers, Sequences

CONSTANTS MaxStrongClones, MaxWeakClones

ASSUME Assumptions == /\ MaxStrongClones > 0
                      /\ MaxWeakClones >= 0
                      
VARIABLES \* strong counter as per algorithm
          strong,
          \* weak counter as per algorithm
          weak,
          \* monotonously growing counter of all strong clones (for the model)
          strongCtr,
          \* monotonously growing counter of all weak clones (for the model)
          weakCtr,
          \* how many times allocated (used to detect double deallocation)
          allocated,
          \* how many times initialized (used to detect double deinitialization)
          initialized,
          \* program counter for strong clones
          strongPc,
          \* program counter for weak clones
          weakPc,
          \* temporary storage used by strong clones
          strongScratchpad,
          \* temporary storage used by weak clones
          weakScratchpad

vars == << strong, weak, strongCtr, weakCtr, allocated, initialized, strongPc, weakPc, strongScratchpad, weakScratchpad >>

\* Ensures variables stay within their bounds
TypeOK == /\ strong >= 0 /\ strong <= MaxStrongClones
          /\ weak >= 0 /\ weak <= MaxWeakClones
          /\ strongCtr >=0 /\ strongCtr <= MaxStrongClones
          /\ weakCtr >=0 /\ weakCtr <= MaxWeakClones
          \* if it ever reaches below 0, there has been a double-free
          \* and 2+ is also nonsense
          /\ allocated \in {1, 0}
          \* if it ever reaches below 0, there has been a double-deinit
          \* and 2+ is also nonsense
          /\ initialized \in {1, 0}
          /\ \A i \in 1..strong: strongPc[i] \in {"none", "ready", "subWeak", "deinit", "deinitialized"}
          /\ \A i \in 1..weak: weakPc[i] \in {"none", "ready", "deinitialized"}
          
Init == /\ strong = 1
        /\ weak = 1
        /\ strongCtr = 1
        /\ weakCtr = 0
        /\ allocated = 1
        /\ initialized = 1
        \* the mere act of RcSp creation establishes one strong clone
        /\ strongPc = [[ x \in (1..MaxStrongClones) |-> "none" ] EXCEPT ![1] = "ready"]
        /\ weakPc = [ x \in (1..MaxWeakClones) |-> "none"]
        /\ strongScratchpad = [ x \in (1..MaxStrongClones) |-> <<>> ]
        /\ weakScratchpad = [ x \in (1..MaxWeakClones) |-> <<>> ]
       

\* Clone strong clone from a strong clone
StrongClone(i) == \/ /\ MaxStrongClones - strongCtr > 0 \* this condition is just to give the model a boundary
                     /\ strongPc[i] = "ready"
                     \* if strong = 0 we can't make any more of strong clones 
                     /\ strong > 0
                     /\ strong' = strong + 1
                     /\ strongCtr' = strongCtr + 1
                     /\ strongPc' = [strongPc EXCEPT ![strongCtr'] = "ready"]
                     /\ UNCHANGED << weak, weakCtr, allocated, initialized, weakPc, strongScratchpad, weakScratchpad >>

\* Clone weak clone from a strong clone
WeakClone(i) == \/ /\ MaxWeakClones - weakCtr - 1 > 0  \* this condition is just to give the model a boundary
                   /\ strongPc[i] = "ready"
                   /\ weak' = weak + 1
                   /\ weakCtr' = weakCtr + 1
                   /\ weakPc' = [weakPc EXCEPT ![weakCtr'] = "ready"]
                   /\ UNCHANGED << strong, strongCtr, allocated, initialized, strongPc, strongScratchpad, weakScratchpad >>

\* Clone strong clone from a weak clone
StrongWeakClone(i) == \/ /\ MaxStrongClones - strongCtr > 0 \* this condition is just to give the model a boundary
                         /\ weakPc[i] = "ready"
                         \* if strong = 0 we can't make any more of strong clones 
                         /\ strong > 0
                         /\ strong' = strong + 1
                         /\ strongCtr' = strongCtr + 1
                         /\ strongPc' = [strongPc EXCEPT ![strongCtr'] = "ready"]
                         /\ UNCHANGED << weak, weakCtr, allocated, initialized, weakPc, strongScratchpad, weakScratchpad >>

\* Clone weak clone from a weak clone
WeakWeakClone(i) == \/ /\ MaxWeakClones - weakCtr - 1 > 0  \* this condition is just to give the model a boundary
                       /\ weakPc[i] = "ready"
                       /\ weak' = weak + 1
                       /\ weakCtr' = weakCtr + 1
                       /\ weakPc' = [weakPc EXCEPT ![weakCtr'] = "ready"]
                       /\ UNCHANGED << strong, strongCtr, allocated, initialized, strongPc, strongScratchpad, weakScratchpad >>
      
\* Drop strong clone
DropStrong(i) == \/ /\ strongPc[i] = "ready"
                    /\ strong' = IF strong = 0 THEN 0 ELSE strong - 1
                    /\ strongPc' = [strongPc EXCEPT ![i] = IF strong = 1 THEN "deinit" ELSE "deinitialized"]
                    /\ strongScratchpad' = [strongScratchpad EXCEPT ![i] = << strong >>]
                    /\ UNCHANGED << weak, allocated, initialized, weakPc, weakScratchpad, strongCtr, weakCtr >>
                 \/ /\ strongPc[i] = "deinit"
                    \* deinitialize if previous strong counter value was 1
                    /\ initialized' = IF strongScratchpad[i][1] = 1 THEN initialized - 1 ELSE initialized
                    /\ strongPc' = [strongPc EXCEPT ![i] = "subWeak" ]
                    /\ UNCHANGED << strong, weak, allocated, weakPc, strongScratchpad, weakScratchpad, strongCtr, weakCtr >>   
                 \/ /\ strongPc[i] = "subWeak"
                    /\ weak' = IF weak = 0 THEN 0 ELSE weak - 1
                    \* deallocate if this was there was only was [virtual] weak clone left
                    /\ allocated' = IF weak = 1 THEN allocated - 1 ELSE allocated
                    \* `inner <- null`
                    /\ strongPc' = [strongPc EXCEPT ![i] = "deinitialized"]
                    /\ UNCHANGED << strong, initialized, weakPc, strongScratchpad, weakScratchpad, strongCtr, weakCtr >>   

\* Drop weak clone
DropWeak(i) == \/ /\ weakPc[i] = "ready"
                  /\ weak' = IF weak = 0 THEN 0 ELSE weak - 1
                  \* if only the very last [virtual] weak clone left
                  /\ allocated' = IF weak = 1 THEN allocated - 1 ELSE allocated
                  \* `inner <- null`
                  /\ weakPc' = [weakPc EXCEPT ![i] = "deinitialized"]
                  /\ UNCHANGED << strong, strongPc, initialized, strongScratchpad, weakScratchpad, strongCtr, weakCtr >>   

Next == \/ \E i \in 1..strongCtr: StrongClone(i)
        \/ \E i \in 1..strongCtr: WeakClone(i)
        \/ \E i \in 1..weakCtr: StrongWeakClone(i)
        \/ \E i \in 1..weakCtr: WeakWeakClone(i)
        \/ \E i \in 1..strongCtr: DropStrong(i)
        \/ \E i \in 1..weakCtr: DropWeak(i)
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

AllStrongClonesDeinitialized == \A i \in 1..strongCtr: strongPc[i] = "deinitialized"
AllWeakClonesDeinitialized == \A i \in 1..weakCtr: weakPc[i] = "deinitialized"
AllClonesDeinitialized == AllStrongClonesDeinitialized /\ AllWeakClonesDeinitialized

Deinitialized == initialized = 0
Deallocated == allocated = 0

Completes == <>(AllClonesDeinitialized /\ Deinitialized /\ Deallocated)


==================================================