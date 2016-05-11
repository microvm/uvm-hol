# Nondet Part 1

The aim of this part of the specification is to model the process whereby a thread maintains a “pile” of pending expression/instruction evaluations, and non-deterministically picks from executable instructions from this pile.

Instructions are added to this pile as they are “fetched”.

In fact, the thread will have to make a non-deterministic choice to either “fetch” or to execute something from the pile.

At the first stage, we could allow fetching to block when a branch is encountered.

The top-level thread relation will look like

    s0 --> s1

if

1. there is a fetchable instruction; s1 is the same as s0 except the pc has moved on, and the instruction at the pc is now part of the pool; or
2. there is an executable instruction $i$ in the pool (where “executable” means that all of its read_vars now have values in the SSA variable map); s1 is the result of executing $i$ on s0.

(At the higher level, steps also occur at the level of all threads and the memory, whose actions will interleave.)

## Ultimate Goal

A specification that we believe, and which has tool support for execution of concrete programs.

## Speculating past Branches

This would require a new state component, say the **speculation context**.  This would be a record of all the branch-decisions that have been assumed. For example, if you had taken branch1, you might record that SSA variable x had to contain zero (so the speculation context would now contain some version of [x=0] in addition to all of the earlier decisions).

There would have to be a check that the speculation context remained consistent at every step.

## Older notes

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

* define `read_vars : instruction -> ssavar set`  (pure syntax)

* define `is_pending : state -> (ssavar -> bool)   =  ssavar set`

* `is_blocked s i ⇔ DISJOINT (is_pending s) (readVars i)`
