(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Computer_Arith.thy                                                   *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* Computer Arithmetic *}

theory Computer_Arith
imports
  Preliminaries
  Strict_Operators
  Machine_Number
  Overflow_Monad
begin

text \<open>This theory might still need a bit more work and development!\<close>

subsection {* Type Definition *}

text \<open>
  To encode the outcome of a computer calculation, we use a type (synonym)
  \<open>'a comparith\<close>. It is an @{type option} type over the machine number type
  @{typ "'a machine_number_ext"}. The latter was introduced in the theory
  @{theory Overflow_Monad}. The order of nesting ensures that we obtain the
  correct strictness properties with respect to \<open>\<bottom>\<close> and \<open>\<top>\<close>, that is \<open>\<bottom>\<close>
  dominates over \<open>\<top>\<close>.
\<close>

type_synonym 'a comparith = "('a machine_number_ext) option"

translations (type) "'a comparith" \<rightleftharpoons> (type) "('a machine_number_ext) option"

text \<open>The notation \<open>\<top>\<close> is introduced for the term @{term "Some Overflow"}.\<close>

definition comparith_top :: "'a::machine_number comparith" where
[simp]: "comparith_top \<equiv> Some Overflow"

adhoc_overloading global_top comparith_top

subsection {* Arithmetic Operators *}

definition plus_comparith ::
  "'a::{plus, machine_number} comparith binop" (infixl "+\<^sub>c" 70) where
[option_ops]: "(op +\<^sub>c) = (op +\<^sub>\<infinity>)\<up>\<^sub>?"

definition minus_comparith ::
  "'a::{minus, machine_number} comparith binop" (infixl "-\<^sub>c" 70) where
[option_ops]: "(op -\<^sub>c) = (op -\<^sub>\<infinity>)\<up>\<^sub>?"

definition time_comparith ::
  "'a::{times, machine_number} comparith binop" (infixl "*\<^sub>c" 70) where
[option_ops]: "(op *\<^sub>c) = (op *\<^sub>\<infinity>)\<up>\<^sub>?"

definition divide_comparith ::
  "'a::{zero, divide, machine_number} comparith binop" (infixl "'/\<^sub>c" 70) where
"x /\<^sub>c y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> 0 then return (x' div\<^sub>\<infinity> y') else \<bottom>}"

declare divide_comparith_def [option_ops]

subsection {* Proof Support *}

method comparith_tac = (option_tac; overflow_tac)
end