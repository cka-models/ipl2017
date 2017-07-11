(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Preliminaries.thy                                                    *)
(******************************************************************************)
(* LAST REVIEWED: 10 July 2017 *)

section {* Preliminaries *}

theory Preliminaries
imports Main Real Eisbach
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Type Synonyms *}

text \<open>Type synonym for homogeneous unary operators on a type @{typ "'a"}.\<close>

type_synonym 'a unop = "'a \<Rightarrow> 'a"

text \<open>Type synonym for homogeneous binary operators on a type @{typ "'a"}.\<close>

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"
end