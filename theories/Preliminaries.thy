(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Preliminaries.thy                                                    *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* Preliminaries *}

theory Preliminaries
imports Main Real Eisbach
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Type Synonyms *}

text \<open>Type synonym for homogeneous relational operators on a type @{typ "'a"}.\<close>

type_synonym 'a relop = "'a \<Rightarrow> 'a \<Rightarrow> bool"

text \<open>Type synonym for homogeneous unary operators on a type @{typ "'a"}.\<close>

type_synonym 'a unop = "'a \<Rightarrow> 'a"

text \<open>Type synonym for homogeneous binary operators on a type @{typ "'a"}.\<close>

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

subsection {* Lattice Syntax *}

text \<open>We use the constants below for ad hoc overloading to avoid ambiguities.\<close>

consts global_bot :: "'a" ("\<bottom>")
consts global_top :: "'a" ("\<top>")

text \<open>Declaration of global notations for lattice operators.\<close>

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65)

notation
  Inf ("\<Sqinter>") and
  Sup ("\<Squnion>")

subsection {* Monad Syntax *}

text \<open>We use the constant below for ad hoc overloading to avoid ambiguities.\<close>

consts return :: "'a \<Rightarrow> 'b" ("return")
end