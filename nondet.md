

* Hol_reln makes inductive definitions

*

   s0 —-> s1

   where s0’s next instruction (as per the program counter) is i, then
   s1 is the same as s0, except that i is now part of the candidate
   execution pile, and the PC is now pointing to the next instruction.

*

    s0 —-> s1

    where s1 is the result of executing an instruction from the candidate execution pile that is not blocked.

*  an instruction is not blocked iff every member of the readVars set has values (is not pending)

* define readVars : instruction -> ssavar set  (pure syntax)

* define isPending : state -> (ssavar -> bool)   =  ssavar set

* isBlocked s i ⇔ DISJOINT (isPending s) (readVars i)
