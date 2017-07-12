(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Overflow_Monad.thy                                                   *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* The Overflow Monad *}

theory Overflow_Monad
imports Machine_Number
begin

subsection {* Type Definition *}

text \<open>Any type with a linear order can be lifted into a type that includes \<open>\<top>\<close>.\<close>

datatype 'a::linorder overflow =
  Value "'a" | Overflow

text \<open>The notation \<open>\<top>\<close> is introduced for the constructor @{const Overflow}.\<close>

adhoc_overloading global_top Overflow

subsection {* Proof Support *}

text \<open>Attribute used to collect definitional laws for operators.\<close>

named_theorems overflow_ops "definitional laws for operators on overflow values"

text \<open>Tactic that facilitates proofs about @{type overflow} values.\<close>

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

method overflow_tac = (
  (atomize (full))?,
  (simp add: split_overflow overflow_ops),
  (clarsimp; simp?)?)

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
-- {* Subgoal 1 *}
apply (overflow_tac)
apply (rule less_le_not_le)
-- {* Subgoal 2 *}
apply (overflow_tac)
-- {* Subgoal 3 *}
apply (overflow_tac)
-- {* Subgoal 4 *}
apply (overflow_tac)
-- {* Subgoal 5 *}
apply (overflow_tac)
done
end

text \<open>More instantiations can be added here as we desire.\<close>

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

adhoc_overloading bind overflow_bind

definition overflow_return :: "'a::linorder \<Rightarrow> 'a overflow" where
[simp]: "overflow_return x = Value x"

adhoc_overloading return overflow_return

subsection \<open>Generic Lifting\<close>

text \<open>Extended machine numbers are machine numbers that record an overflow.\<close>

type_synonym 'a machine_number_ext = "'a machine_number overflow"

translations
  (type) "'a machine_number_ext" \<leftharpoondown> (type) "'a machine_number overflow"

text \<open>We use the constant below for ad hoc overloading to avoid ambiguities.\<close>

consts lift_overflow :: "'a \<Rightarrow> 'b" ("_\<up>\<^sub>\<infinity>" [1000] 1000)

default_sort machine_number

definition ulift_overflow ::
  "('a \<Rightarrow> 'b) \<Rightarrow>
   ('a machine_number_ext \<Rightarrow> 'b machine_number_ext)" where
"ulift_overflow f x =
  do {x' \<leftarrow> x; if (f \<lbrakk>x'\<rbrakk>) \<in> number_range then return MN(f \<lbrakk>x'\<rbrakk>) else \<top>}"

definition blift_overflow ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>
   ('a machine_number_ext \<Rightarrow> 'b machine_number_ext \<Rightarrow> 'c machine_number_ext)" where
"blift_overflow f x y = do {x' \<leftarrow> x; y' \<leftarrow> y;
  if (f \<lbrakk>x'\<rbrakk> \<lbrakk>y'\<rbrakk>) \<in> number_range then return MN(f \<lbrakk>x'\<rbrakk> \<lbrakk>y'\<rbrakk>) else \<top>}"

default_sort type

adhoc_overloading lift_overflow ulift_overflow
adhoc_overloading lift_overflow blift_overflow

text \<open>Note that we do not add the above operators to @{attribute overflow_ops}.\<close>

lemma ulift_overflow_simps [simp]:
"ulift_overflow f \<top> = \<top>"
"ulift_overflow f (Value x) =
  (if (f \<lbrakk>x\<rbrakk>) \<le> max_number then Value MN(f \<lbrakk>x\<rbrakk>) else \<top>)"
apply (unfold ulift_overflow_def)
apply (simp_all)
done

lemma blift_overflow_simps [simp]:
"blift_overflow f x \<top> = \<top>"
"blift_overflow f \<top> y = \<top>"
"blift_overflow f (Value x') (Value y') =
  (if (f \<lbrakk>x'\<rbrakk> \<lbrakk>y'\<rbrakk>) \<le> max_number then Value MN(f \<lbrakk>x'\<rbrakk> \<lbrakk>y'\<rbrakk>) else \<top>)"
apply (unfold blift_overflow_def)
apply (simp_all)
apply (case_tac x; simp)
done

subsection \<open>Lifted Operators\<close>

definition plus_overflow::
  "'a::{plus, machine_number} machine_number_ext binop" (infixl "+\<^sub>\<infinity>" 70) where
"plus_overflow = (op +)\<up>\<^sub>\<infinity>"

definition minus_overflow ::
  "'a::{minus, machine_number} machine_number_ext binop" (infixl "-\<^sub>\<infinity>" 70) where
"minus_overflow = (op -)\<up>\<^sub>\<infinity>"

definition times_overflow::
  "'a::{times, machine_number} machine_number_ext binop" (infixl "*\<^sub>\<infinity>" 70) where
"times_overflow = (op *)\<up>\<^sub>\<infinity>"

definition divide_overflow ::
  "'a::{divide, machine_number} machine_number_ext binop" (infixl "div\<^sub>\<infinity>" 70) where
"divide_overflow = (op div)\<up>\<^sub>\<infinity>"

paragraph {* Proof Support *}

declare plus_overflow_def [overflow_ops]
declare minus_overflow_def [overflow_ops]
declare times_overflow_def [overflow_ops]
declare divide_overflow_def [overflow_ops]

subsection {* Instantiation Example *}

text \<open>We give an instantiation for natural numbers.\<close>

instantiation nat :: machine_number
begin
definition max_number_nat :: "nat" where
"max_number_nat = 2 ^^ 32 - 1"
instance ..
end

subsection {* Proof Experiments *}

lemma
fixes x :: "nat machine_number_ext"
fixes y :: "nat machine_number_ext"
shows "x *\<^sub>\<infinity> y = y *\<^sub>\<infinity> x"
-- \<open>Is there another way to turn free variables in meta-quantified ones?\<close>
apply (transfer)
apply (overflow_tac)
apply (simp add: mult.commute)
done

text \<open>Yes, using the below. Turn this into a tactic command! [TODO]\<close>

ML {* Induct.arbitrary_tac *}
end