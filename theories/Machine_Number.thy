(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Machine_Number.thy                                                   *)
(******************************************************************************)

section {* Machine Numbers *}

theory Machine_Number
imports Main
begin

text \<open>Type synonym for a binary operator on a type @{typ "'a"}.\<close>

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

subsection {* Type Class *}

text \<open>
  Machine numbers are introduced via a type class \<open>machine_number\<close>. The class
  is an extension of a linear order and introduces a constant that yields the
  maximum representable number. An assumption of the class is that there exists
  at least one valid machine number.
\<close>

class machine_number = linorder +
  fixes max_number :: "'a"
  assumes machine_number_exists: "\<exists>x. x \<le> max_number"
begin

text \<open>All numbers less or equal to @{const max_number} are within range.\<close>

definition number_range :: "'a set" where
[simp]: "number_range = {x. x \<le> max_number}"
end

subsection {* Type Definition *}

text \<open>We furthermore introduce a type definition for machine numbers.\<close>

typedef (overloaded)
  'a::machine_number machine_number = "number_range::'a set"
apply (unfold number_range_def)
apply (clarsimp)
apply (rule machine_number_exists)
done

notation Abs_machine_number ("MN'(_')")

text \<open>The syntax \<open>\<lbrakk>_\<rbrakk>\<close> is introduced for the representation function.\<close>

notation Rep_machine_number ("\<lbrakk>_\<rbrakk>")

setup_lifting type_definition_machine_number

paragraph {* Proof Support *}

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

instantiation machine_number :: (machine_number) linorder
begin
definition less_eq_machine_number ::
  "'a machine_number \<Rightarrow> 'a machine_number \<Rightarrow> bool" where
[simp]: "less_eq_machine_number x y = (\<lbrakk>x\<rbrakk> \<le> \<lbrakk>y\<rbrakk>)"
definition less_machine_number ::
  "'a machine_number \<Rightarrow> 'a machine_number \<Rightarrow> bool" where
[simp]: "less_machine_number x y = (\<lbrakk>x\<rbrakk> < \<lbrakk>y\<rbrakk>)"
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

instantiation machine_number :: ("{machine_number,zero}") zero
begin
definition zero_machine_number :: "'a machine_number" where
[simp]: "zero_machine_number = MN(0)"
instance ..
end

instantiation machine_number :: ("{machine_number,one}") one
begin
definition one_machine_number :: "'a machine_number" where
[simp]: "one_machine_number = MN(1)"
instance ..
end

instantiation machine_number :: ("{machine_number,plus}") plus
begin
definition plus_machine_number :: "'a machine_number binop" where
[simp]: "plus_machine_number x y = MN(\<lbrakk>x\<rbrakk> + \<lbrakk>y\<rbrakk>)"
instance ..
end

instantiation machine_number :: ("{machine_number,minus}") minus
begin
definition minus_machine_number :: "'a machine_number binop" where
[simp]: "minus_machine_number x y = MN(\<lbrakk>x\<rbrakk> - \<lbrakk>y\<rbrakk>)"
instance ..
end

instantiation machine_number :: ("{machine_number,times}") times
begin
definition times_machine_number :: "'a machine_number binop" where
[simp]: "times_machine_number x y = MN(\<lbrakk>x\<rbrakk> * \<lbrakk>y\<rbrakk>)"
instance ..
end

instantiation machine_number :: ("{machine_number,divide}") divide
begin
definition divide_machine_number :: "'a machine_number binop" where
[simp]: "divide_machine_number x y = MN(\<lbrakk>x\<rbrakk> div \<lbrakk>y\<rbrakk>)"
instance ..
end
end