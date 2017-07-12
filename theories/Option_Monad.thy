(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Option_Monad.thy                                                     *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* The Option Monad *}

theory Option_Monad
imports Preliminaries
  "~~/src/HOL/Library/Option_ord"
begin

text \<open>
  Whilst Isabelle/HOL already provides an encoding of the @{type option} type
  and monad, we include a few supplementary definitions and tactics here that
  are useful for readability and automatic proof later on.
\<close>

subsection {* Syntax and Definitions *}

text \<open>The notation \<open>\<bottom>\<close> is introduced for the constructor @{const None}.\<close>

adhoc_overloading global_bot None

text \<open>We moreover define a \<open>return\<close> function for the @{type option} monad.\<close>

definition option_return :: "'a \<Rightarrow> 'a option" where
[simp]: "option_return x = Some x"

adhoc_overloading return option_return

text \<open>Note that @{const bind} is already defined for type @{type option}.\<close>

subsection {* Instantiations *}

text \<open>More instantiations can be added here as we desire.\<close>

instantiation option :: (zero) zero
begin
definition zero_option :: "'a option" where
[simp]: "zero_option = Some 0"
instance ..
end

instantiation option :: (one) one
begin
definition one_option :: "'a option" where
[simp]: "one_option = Some 1"
instance ..
end

subsection {* Proof Support *}

text \<open>Attribute used to collect definitional laws for operators.\<close>

named_theorems option_ops "definitional laws for operators on option values"

text \<open>Tactic that facilitates proofs about @{type option} values.\<close>

lemmas split_option =
  split_option_all
  split_option_ex

method option_tac = (
  (atomize (full))?,
  (simp add: split_option option_ops),
  (clarsimp; simp?)?)
end