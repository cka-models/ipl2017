(******************************************************************************)
(* Project: The Interchange Law in Application to Concurrent Programming      *)
(* File: Overflow_Monad.thy                                                   *)
(* Authors: Frank Zeyda, Tony Hoare and Georg Struth                          *)
(******************************************************************************)

section {* The Overflow Monad *}

theory Overflow_Monad
imports Main "~~/src/HOL/Library/Monad_Syntax" Eisbach
begin

subsection {* Type Definition *}

datatype 'a::linorder overflow =
  Result "'a" | Overflow ("\<top>")

subsection {* Ordering Relation *}

instantiation overflow :: (linorder) linorder
begin
fun less_eq_overflow :: "'a overflow \<Rightarrow> 'a overflow \<Rightarrow> bool" where
"Result x \<le> Result y \<longleftrightarrow> x \<le> y" |
"Result x \<le> Overflow \<longleftrightarrow> True" |
"Overflow \<le> Result x \<longleftrightarrow> False" |
"Overflow \<le> Overflow \<longleftrightarrow> True"
fun less_overflow :: "'a overflow \<Rightarrow> 'a overflow \<Rightarrow> bool" where
"Result x < Result y \<longleftrightarrow> x < y" |
"Result x < Overflow \<longleftrightarrow> True" |
"Overflow < Result x \<longleftrightarrow> False" |
"Overflow < Overflow \<longleftrightarrow> False"
instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (induct_tac x; induct_tac y; simp)
using le_less apply (auto) [1]
-- {* Subgoal 2 *}
apply (induct_tac x; simp)
-- {* Subgoal 3 *}
apply (unfold atomize_imp)
apply (induct_tac x; induct_tac y; induct_tac z; simp)
using order_trans apply (blast)
-- {* Subgoal 4 *}
apply (induct_tac x; induct_tac y; simp)
-- {* Subgoal 5 *}
apply (induct_tac x; induct_tac y; simp)
using le_cases apply (blast)
done
end

subsection {* Monadic Constructors *}

primrec overflow_bind ::
  "'a::linorder overflow \<Rightarrow> ('a \<Rightarrow> 'b::linorder overflow) \<Rightarrow> 'b overflow" where
"overflow_bind Overflow f = Overflow" |
"overflow_bind (Result x) f = f x"

adhoc_overloading
  bind overflow_bind

definition overflow_return :: "'a::linorder \<Rightarrow> 'a overflow" ("return") where
[simp]: "overflow_return x = Result x"

subsection {* Lifted Operators *}

text \<open>Attribute used to collection definitional laws for lifted operators.\<close>

named_theorems overflow_monad_ops
  "definitial laws for lifted operators into the overflow monad"

consts max_value :: "'a"

text {*
  Tony, I think the definition below is not quite right! It is not just enough
  to check that @{term "(f x' y') \<le> max_value"} since this does not imply that
  both @{term "x' \<le> max_value"} and @{term "y' \<le> max_value"}. Consider, for
  instance, @{term "0*y \<le> max_value"} for any @{term y} (!).
*}

definition check_overflow ::
  "('a::linorder \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   ('a overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow)" where
[overflow_monad_ops]: "check_overflow f x y =
  do {x' \<leftarrow> x; y' \<leftarrow> y; if (f x' y') \<le> max_value then return (f x' y') else \<top>}"

definition overflow_times ::
  "'a::{times,linorder} overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow"
  (infixl "[*]" 70) where
[overflow_monad_ops]: "overflow_times = check_overflow (op *)"

definition overflow_divide ::
  "'a::{divide,linorder} overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow"
  (infixl "[div]" 70) where
[overflow_monad_ops]: "overflow_divide = check_overflow (op div)"

subsection {* Proof Support *}

text \<open>Proof support for reasoning about @{type overflow} types.\<close>

lemma split_overflow_all:
"(\<forall>x::'a::linorder overflow. P x) = (P Overflow \<and> (\<forall>x::'a. P (Result x)))"
apply (safe; simp?)
apply (case_tac x)
apply (simp_all)
done

lemma split_overflow_ex:
"(\<exists>x::'a::linorder overflow. P x) = (P Overflow \<or> (\<exists>x::'a. P (Result x)))"
apply (safe; simp?)
apply (case_tac x)
apply (simp_all) [2]
apply (auto)
done

text \<open>Tactic that performs automatic case splittings for the @{type overflow} type.\<close>

lemmas split_overflow =
  split_overflow_all split_overflow_ex

method overflow_tac = (
  (atomize (full))?,
  ((unfold overflow_monad_ops overflow_return_def)?) [1],
  (simp add: split_overflow)?)

subsection {* Proof Experiments *}

lemma "\<forall>(x::nat overflow) y. x [*] y = y [*] x"
apply (overflow_tac)
apply (simp add: semiring_normalization_rules(7))
done
end