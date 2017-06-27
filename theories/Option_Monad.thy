(******************************************************************************)
(* Project: The Interchange Law in Application to Concurrent Programming      *)
(* File: Option_Monad.thy                                                     *)
(* Authors: Frank Zeyda, Tony Hoare and Georg Struth                          *)
(******************************************************************************)

section {* The Option Monad: Supplement *}

theory Option_Monad
imports "~~/src/HOL/Library/Monad_Syntax" Eisbach
begin

text \<open>
  While Isabelle/HOL already provides an encoding of the @{type option} type
  and monad, we include a few supplementary definitions and tactics here that
  are useful for readability and automatic proof.
\<close>

subsection {* Syntax and Definitions *}

text \<open>The \<open>return\<close> function of the option monad (bind is already defined).\<close>

definition option_return :: "'a \<Rightarrow> 'a option" ("return") where
[simp]: "option_return x = Some x"

text \<open>We introduce the notation \<open>\<bottom>\<close> for @{const None}.\<close>

notation None ("\<bottom>")

subsection {* Proof Support *}

text \<open>Proof support for reasoning about @{type option} types.\<close>

text \<open>Attribute used to collection definitional laws for lifted operators.\<close>

named_theorems option_monad_ops
  "definitial laws for lifted operators into the option monad"

text \<open>Tactic that facilitates proofs about the @{type option} type.\<close>

lemmas split_option =
  split_option_all
  split_option_ex

method option_tac = (
  (atomize (full))?,
  ((unfold option_monad_ops option_return_def)?) [1],
  (simp add: split_option)?)
end