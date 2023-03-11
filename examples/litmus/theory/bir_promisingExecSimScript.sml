open HolKernel Parse boolLib bossLib BasicProvers
open bir_promisingTheory bir_programTheory
open bir_promisingExecTheory
open listTheory rich_listTheory
open arithmeticTheory
open relationTheory
open finite_mapTheory
open optionTheory
open quantHeuristicsTheory

val _ = new_theory "bir_promisingExecSim";



val _ = export_theory();
