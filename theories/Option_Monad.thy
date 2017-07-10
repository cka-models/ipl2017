(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Option_Monad.thy                                                     *)
(******************************************************************************)

section {* The Option Monad: Supplement *}

theory Option_Monad
imports Eisbach
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Option_ord"
begin

text \<open>
  While Isabelle/HOL already provides an encoding of the @{type option} type
  and monad, we include a few supplementary definitions and tactics here that
  are useful for readability and automatic proof.
\<close>

subsection {* Syntax and Definitions *}

text \<open>The \<open>return\<close> function of the option monad. (Bind is already defined.)\<close>

definition option_return :: "'a \<Rightarrow> 'a option" ("return") where
[simp]: "option_return x = Some x"

text \<open>We introduce the notation \<open>\<bottom>\<close> for the constructor @{const None}.\<close>

notation None ("\<bottom>")

subsection {* Instantiations *}

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
  (simp add: split_option zero_option_def one_option_def)?)
end