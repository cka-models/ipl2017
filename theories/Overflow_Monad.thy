(******************************************************************************)
(* Project: The Interchange Law in Application to Concurrent Programming      *)
(* File: Overflow_Monad.thy                                                   *)
(* Authors: Frank Zeyda, Tony Hoare and Georg Struth                          *)
(******************************************************************************)

section {* The Overflow Monad *}

theory Overflow_Monad
imports Main Groups "~~/src/HOL/Library/Monad_Syntax" Eisbach
begin

subsection {* Type Definition *}

datatype 'a::linorder overflow =
  Value "'a" | Overflow ("\<top>")

subsection {* Ordering Relation *}

instantiation overflow :: (linorder) linorder
begin
fun less_eq_overflow :: "'a overflow \<Rightarrow> 'a overflow \<Rightarrow> bool" where
"Value x \<le> Value y \<longleftrightarrow> x \<le> y" |
"Value x \<le> Overflow \<longleftrightarrow> True" |
"Overflow \<le> Value x \<longleftrightarrow> False" |
"Overflow \<le> Overflow \<longleftrightarrow> True"

fun less_overflow :: "'a overflow \<Rightarrow> 'a overflow \<Rightarrow> bool" where
"Value x < Value y \<longleftrightarrow> x < y" |
"Value x < Overflow \<longleftrightarrow> True" |
"Overflow < Value x \<longleftrightarrow> False" |
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

instantiation overflow :: ("{linorder, zero}") zero
begin
definition zero_overflow :: "'a overflow" where
[simp]: "zero_overflow = Value 0"
instance ..
end

instantiation overflow :: ("{linorder, one}") one
begin
definition one_overflow :: "'a overflow" where
[simp]: "one_overflow = Value 1"
instance ..
end

subsection {* Monadic Constructors *}

primrec overflow_bind ::
  "'a::linorder overflow \<Rightarrow> ('a \<Rightarrow> 'b::linorder overflow) \<Rightarrow> 'b overflow" where
"overflow_bind Overflow f = Overflow" |
"overflow_bind (Value x) f = f x"

adhoc_overloading
  bind overflow_bind

definition overflow_return :: "'a::linorder \<Rightarrow> 'a overflow" ("return") where
[simp]: "overflow_return x = Value x"

subsection {* Lifted Operators *}

text \<open>Attribute used to collection definitional laws for lifted operators.\<close>

named_theorems overflow_monad_ops
  "definitial laws for lifted operators into the overflow monad"

text \<open>Polymorphic constant for the maximal admissible value of some type.\<close>

consts max_value :: "'a"

paragraph \<open>Generic Lifting Functor\<close>

text {*
  I believe the definition below is not quite correct. We also need to check
  that \<open>x' \<le> max_value\<close> and \<open>y' \<le> max_value\<close> in the conditional. Not doing
  so gives rise to a counterexample to the ICL instance in Section 3. Namely,
  by choosing \<open>p = 0\<close>, \<open>r = 1\<close> and \<open>s = 1\<close> we can derive \<open>\<top> \<le> 0\<close> if choosing
  some \<open>q > max_value\<close>.
*}

definition check_overflow ::
  "('a::linorder \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   ('a overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow)" where
[overflow_monad_ops]:
"check_overflow f x y =
  do {x' \<leftarrow> x; y' \<leftarrow> y; if (f x' y') \<le> max_value then return (f x' y') else \<top>}"

paragraph \<open>Concrete Lifted Operators\<close>

definition overflow_times ::
  "'a::{times,linorder} overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow"
  (infixl "[*]" 70) where
[overflow_monad_ops]: "overflow_times = check_overflow (op *)"

definition overflow_divide ::
  "'a::{divide,linorder} overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow"
  (infixl "[div]" 70) where
[overflow_monad_ops]: "overflow_divide = check_overflow (op div)"

subsection {* Laws *}

lemma check_overflow_simps [simp]:
"check_overflow f x \<top> = \<top>"
"check_overflow f \<top> y = \<top>"
apply (unfold check_overflow_def)
apply (case_tac x; simp)
apply (case_tac y; simp)
done

lemma check_overflow_Value (*[simp]*):
"check_overflow f (Value x) (Value y) =
  (if (f x y) \<le> max_value then Value (f x y) else \<top>)"
apply (unfold check_overflow_def)
apply (case_tac "(f x y) \<le> max_value")
apply (simp_all)
done

subsection {* Proof Support *}

text \<open>Proof support for reasoning about @{type overflow} types.\<close>

lemma split_overflow_all:
"(\<forall>x. P x) = (P Overflow \<and> (\<forall>x. P (Value x)))"
apply (safe)
-- {* Subgoal 1 *}
apply (clarsimp)
-- {* Subgoal 2 *}
apply (clarsimp)
-- {* Subgoal 3 *}
apply (case_tac x)
apply (simp_all)
done

lemma split_overflow_ex:
"(\<exists>x. P x) = (P Overflow \<or> (\<exists>x. P (Value x)))"
apply (safe)
-- {* Subgoal 1 *}
apply (case_tac x)
apply (simp_all) [2]
-- {* Subgoal 2 *}
apply (auto) [1]
-- {* Subgoal 3 *}
apply (auto) [1]
done

lemmas split_overflow =
  split_overflow_all
  split_overflow_ex

text \<open>Tactic that facilitates proofs about the @{type overflow} type.\<close>

method overflow_tac = (
  (atomize (full))?,
  ((unfold overflow_monad_ops overflow_return_def)?) [1],
  (simp add: split_overflow)?)

subsection {* Proof Experiments *}

lemma "\<And>(x::nat overflow) y. x [*] y = y [*] x"
apply (overflow_tac)
apply (simp add: semiring_normalization_rules(7))
done
end