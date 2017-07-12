(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Machine_Number.thy                                                   *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* Machine Numbers *}

theory Machine_Number
imports Preliminaries
begin

subsection {* Type Class *}

text \<open>
  Machine numbers are introduced via a type class \<open>machine_number\<close>. The class
  extends a linear order by including a constant \<open>max_number\<close> that yields the
  largest representable number.
\<close>

class machine_number = linorder +
  fixes max_number :: "'a"
begin

text \<open>All numbers less or equal to @{const max_number} are within range.\<close>

definition number_range :: "'a set" where
[simp]: "number_range = {x. x \<le> max_number}"
end

text \<open>We can easily prove that @{const number_range} is a non-empty set.\<close>

lemma ex_leq_max_number:
"\<exists>x. x \<le> max_number"
apply (rule_tac x = "max_number" in exI)
apply (rule order_refl)
done

lemma ex_in_number_range:
"\<exists>x. x \<in> number_range"
apply (clarsimp)
apply (rule ex_leq_max_number)
done

subsection {* Type Definition *}

text \<open>The above lemma enables us to introduce a type for representable numbers.\<close>

typedef (overloaded)
  'a::machine_number machine_number = "number_range::'a set"
apply (rule ex_in_number_range)
done

text \<open>The notation \<open>MN(_)\<close> will be used for the abstraction function.\<close>

notation Abs_machine_number ("MN'(_')")

text \<open>The notation \<open>\<lbrakk>_\<rbrakk>\<close> will be used for the representation function.\<close>

notation Rep_machine_number ("\<lbrakk>_\<rbrakk>")

setup_lifting type_definition_machine_number

subsection {* Proof Support *}

lemmas Rep_machine_number_inject_sym = sym [OF Rep_machine_number_inject]

declare Abs_machine_number_inverse
  [simplified number_range_def mem_Collect_eq, simp]

declare Rep_machine_number_inverse
  [simplified number_range_def mem_Collect_eq, simp]

declare Abs_machine_number_inject
  [simplified number_range_def mem_Collect_eq, simp]

declare Rep_machine_number_inject_sym
  [simplified number_range_def mem_Collect_eq, simp]

subsection {* Instantiations *}

subsubsection {* Linear Order *}

instantiation machine_number :: (machine_number) linorder
begin
definition less_eq_machine_number ::
  "'a machine_number \<Rightarrow> 'a machine_number \<Rightarrow> bool" where
[simp]: "less_eq_machine_number x y \<longleftrightarrow> \<lbrakk>x\<rbrakk> \<le> \<lbrakk>y\<rbrakk>"

definition less_machine_number ::
  "'a machine_number \<Rightarrow> 'a machine_number \<Rightarrow> bool" where
[simp]: "less_machine_number x y \<longleftrightarrow> \<lbrakk>x\<rbrakk> < \<lbrakk>y\<rbrakk>"
instance
apply (intro_classes)
apply (unfold less_eq_machine_number_def less_machine_number_def)
-- {* Subgoal 1 *}
apply (transfer')
apply (rule less_le_not_le)
-- {* Subgoal 2 *}
apply (transfer')
apply (rule order_refl)
-- {* Subgoal 3 *}
apply (transfer')
apply (erule order_trans)
apply (assumption)
-- {* Subgoal 4 *}
apply (transfer')
apply (erule antisym)
apply (assumption)
-- {* Subgoal 5 *}
apply (transfer')
apply (rule linear)
done
end

subsubsection {* Arithmetic Operators *}

instantiation machine_number :: ("{machine_number, zero}") zero
begin
definition zero_machine_number :: "'a machine_number" where
[simp]: "zero_machine_number = MN(0)"
instance ..
end

instantiation machine_number :: ("{machine_number, one}") one
begin
definition one_machine_number :: "'a machine_number" where
[simp]: "one_machine_number = MN(1)"
instance ..
end

instantiation machine_number :: ("{machine_number, plus}") plus
begin
definition plus_machine_number :: "'a machine_number binop" where
[simp]: "plus_machine_number x y = MN(\<lbrakk>x\<rbrakk> + \<lbrakk>y\<rbrakk>)"
instance ..
end

instantiation machine_number :: ("{machine_number, minus}") minus
begin
definition minus_machine_number :: "'a machine_number binop" where
[simp]: "minus_machine_number x y = MN(\<lbrakk>x\<rbrakk> - \<lbrakk>y\<rbrakk>)"
instance ..
end

instantiation machine_number :: ("{machine_number, times}") times
begin
definition times_machine_number :: "'a machine_number binop" where
[simp]: "times_machine_number x y = MN(\<lbrakk>x\<rbrakk> * \<lbrakk>y\<rbrakk>)"
instance ..
end

instantiation machine_number :: ("{machine_number, divide}") divide
begin
definition divide_machine_number :: "'a machine_number binop" where
[simp]: "divide_machine_number x y = MN(\<lbrakk>x\<rbrakk> div \<lbrakk>y\<rbrakk>)"
instance ..
end
end