open HolKernel Parse boolLib bossLib;

open uvmMemoryModelTheory;
open uvmThreadSemanticsTheory;


val _ = new_theory "uvmSystem"; 

val _ = export_theory();
