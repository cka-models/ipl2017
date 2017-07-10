(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Overflow_Monad.thy                                                   *)
(******************************************************************************)

section {* The Overflow Monad *}

theory Overflow_Monad
imports Machine_Number
  Main Real Groups "~~/src/HOL/Library/Monad_Syntax" Eisbach
begin

text \<open>Type synonym for a binary operator on a type @{typ "'a"}.\<close>

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

subsection {* Type Definition *}

text \<open>Any type with a linear order can be lifted into a type that includes \<open>\<top>\<close>.\<close>

datatype 'a::linorder overflow =
  Value "'a" |
  Overflow ("\<top>")

subsection {* Ordering Relation *}

text \<open>Overflow (\<open>\<top>\<close>) resides above any other value in the order.\<close>

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
apply (unfold atomize_imp)
-- {* Subgoal 1 *}
apply (induct_tac x; induct_tac y; simp)
apply (rule less_le_not_le)
-- {* Subgoal 2 *}
apply (induct_tac x; simp)
-- {* Subgoal 3 *}
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

text \<open>To support monadic syntax, we define the bind and return functions below.\<close>

primrec overflow_bind ::
  "'a::linorder overflow \<Rightarrow> ('a \<Rightarrow> 'b::linorder overflow) \<Rightarrow> 'b overflow" where
"overflow_bind (Overflow) f = Overflow" |
"overflow_bind (Value x)  f = f x"

adhoc_overloading
  bind overflow_bind

definition overflow_return :: "'a::linorder \<Rightarrow> 'a overflow" ("return") where
[simp]: "overflow_return x = Value x"

subsection {* Lifted Operators *}

text \<open>Attribute used to collection definitional laws for lifted operators.\<close>

named_theorems overflow_monad_ops
  "definitial laws for lifted operators into the overflow monad"

paragraph \<open>Generic Lifting Functor\<close>

default_sort machine_number

text \<open>Extended machine numbers are machine numbers that record an overflow.\<close>

type_synonym 'a machine_number_ext = "'a machine_number overflow"

definition check_overflow :: "'a binop \<Rightarrow> 'a machine_number_ext binop" where
[overflow_monad_ops]:
"check_overflow f x y =
  do {x' \<leftarrow> x; y' \<leftarrow> y;
    if (f \<lbrakk>x'\<rbrakk> \<lbrakk>y'\<rbrakk>) \<in> number_range then return MN(f \<lbrakk>x'\<rbrakk> \<lbrakk>y'\<rbrakk>) else \<top>}"

paragraph \<open>Concrete Lifted Operators\<close>

definition overflow_times ::
  "'a::{times,machine_number} machine_number_ext binop" (infixl "[*]" 70) where
[overflow_monad_ops]: "overflow_times = check_overflow (op *)"

definition overflow_divide ::
  "'a::{divide,machine_number} machine_number_ext binop"
  (infixl "[div]" 70) where
[overflow_monad_ops]: "overflow_divide = check_overflow (op div)"

default_sort type

subsection {* Overflow Laws *}

lemma check_overflow_simps [simp]:
"check_overflow f x \<top> = \<top>"
"check_overflow f \<top> y = \<top>"
apply (unfold check_overflow_def)
apply (case_tac x; simp)
apply (case_tac y; simp)
done

lemma check_overflow_Value [simp]:
"check_overflow f (Value x) (Value y) =
  (if (f \<lbrakk>x\<rbrakk> \<lbrakk>y\<rbrakk>) \<le> max_number then Value (MN(f \<lbrakk>x\<rbrakk> \<lbrakk>y\<rbrakk>)) else \<top>)"
apply (unfold check_overflow_def)
apply (clarsimp)
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

instantiation nat :: machine_number
begin
definition max_number_nat :: "nat" where
"max_number_nat = 2 ^^ 31"
instance
apply (intro_classes)
apply (unfold max_number_nat_def)
apply (rule_tac x = "0" in exI)
apply (simp)
done
end

lemma "\<And>(x::nat machine_number_ext) y. x [*] y = y [*] x"
apply (overflow_tac)
apply (simp add: semiring_normalization_rules(7))
done
end