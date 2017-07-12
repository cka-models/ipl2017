(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: ICL_Examples.thy                                                     *)
(******************************************************************************)
(* LAST REVIEWED: TODO *)

section {* Example Applications *}

theory ICL_Examples
imports ICL Strict_Operators Computer_Arith Partiality
begin

hide_const Partiality.Value

text \<open>Example applications of the interchange law from the working note.\<close>

subsection \<open>Arithmetic: addition (\<open>+\<close>) and subtraction (\<open>-\<close>) of numbers.\<close>

text \<open>
  We prove the ICL for the HOL types @{type int}, @{type rat} and @{type real},
  as well as the corresponding @{type option} type instances of those types.
\<close>

-- \<open>Note that the law does not hold for type @{type nat}.\<close>

interpretation icl_plus_minus_nat:
  iclaw "TYPE(nat)" "op =" "op +" "op -"
apply (unfold_locales)
apply (linarith?)
oops

interpretation icl_plus_minus_int:
  iclaw "TYPE(int)" "op =" "op +" "op -"
apply (unfold_locales)
apply (linarith)
done

interpretation icl_plus_minus_rat:
  iclaw "TYPE(rat)" "op =" "op +" "op -"
apply (unfold_locales)
apply (linarith)
done

interpretation icl_plus_minus_real:
  iclaw "TYPE(real)" "op =" "op +" "op -"
apply (unfold_locales)
apply (linarith)
done

text \<open>Corresponding ICL proofs for option types and strict operators.\<close>

interpretation icl_plus_minus_int_option:
  iclaw "TYPE(int option)" "op =\<^sub>?" "op +\<^sub>?" "op -\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_plus_minus_rat_option:
  iclaw "TYPE(rat option)" "op =\<^sub>?" "op +\<^sub>?" "op -\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_plus_minus_real_option:
  iclaw "TYPE(real option)" "op =\<^sub>?" "op +\<^sub>?" "op -\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

subsection \<open>Arithmetic: multiplication (\<open>x\<close>) and division (\<open>/\<close>) of numbers.\<close>

text \<open>This is proved for @{type rat}, @{type real}, and option types thereof.\<close>

interpretation icl_mult_div_rat:
  iclaw "TYPE(rat)" "op =" "op *" "op /"
apply (unfold_locales)
apply (simp)
done

interpretation icl_mult_div_real:
  iclaw "TYPE(real)" "op =" "op *" "op /"
apply (unfold_locales)
apply (simp)
done

interpretation icl_mult_div_rat_option:
  iclaw "TYPE(rat option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_mult_div_real_real:
  iclaw "TYPE(real option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

text \<open>The theorem below holds for any @{class division_ring}...\<close>

context division_ring
begin
lemma div_mult_exchange:
fixes p :: "'a"
fixes q :: "'a"
shows "(p / q) * q = (p * q) / q"
apply (metis eq_divide_eq mult_eq_0_iff)
done
end

text \<open>... and hence for @{type rat}ional and @{type real} numbers.\<close>

lemma rat_div_mult_exchange:
fixes p :: "rat"
fixes q :: "rat"
shows "(p / q) * q = (p * q) / q"
apply (rule div_mult_exchange)
done

lemma real_div_mult_exchange:
fixes p :: "real"
fixes q :: "real"
shows "(p / q) * q = (p * q) / q"
apply (rule div_mult_exchange)
done

subsection \<open>Natural numbers: multiplication (\<open>x\<close>) and truncated division (\<open>-:-\<close>).\<close>

text \<open>We note that @{term "x div y"} is used in Isabelle for truncated division.\<close>

text \<open>We first prove the lemma below which is also described in the paper.\<close>

lemma nat_div_mult_leq:
fixes p :: "nat"
fixes q :: "nat"
-- {* The assumption \<open>q > 0\<close> is not needed because of \<open>x div 0 = 0\<close>. *}
shows "(p div q) * q \<le> (p * q) div q"
apply (case_tac "q > 0")
apply (metis div_mult_self_is_m mult.commute split_div_lemma)
apply (simp)
done

text \<open>
  Since Isabelle/HOL defines \<open>x div 0 = 0\<close>, we can prove the interchange law
  even in HOL's weak treatment of undefinedness, as well as our strong one.
\<close>

interpretation icl_mult_trunc_div_nat:
  iclaw "TYPE(nat)" "op \<le>" "op *" "op div"
apply (unfold_locales)
apply (case_tac "r = 0"; simp_all)
apply (case_tac "s = 0"; simp_all)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis div_mult_self_is_m mult_le_mono nat_div_mult_leq)
done

interpretation icl_mult_trunc_div_nat_option:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (rule icl_mult_trunc_div_nat.interchange_law)
done

subsection \<open>Propositional calculus: conjunction (\<open>\<and>\<close>) and implication (\<open>\<Rightarrow>\<close>).\<close>

text \<open>RE: Implication \<open>p \<Rightarrow> q\<close> is defined in the usual way as \<open>\<not>p \<or> q\<close>.\<close>

text \<open>We can easily verify the above equivalence in HOL.\<close>

lemma "(p \<longrightarrow> q) \<equiv> (\<not> p \<or> q)"
apply (auto)
done

text \<open>We note that \<open>\<turnstile>\<close> is encoded by object-logic implication (\<open>\<longrightarrow>\<close>).\<close>

definition turnstile :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<turnstile>" 50) where
[iff]: "turnstile p q \<equiv> p \<longrightarrow> q"

interpretation icl_imp_conj:
  iclaw "TYPE(bool)" "op \<longrightarrow>" "op \<and>" "op \<turnstile>"
apply (unfold_locales)
apply (auto)
done

subsection \<open>Boolean Algebra: conjunction (\<open>\<and>\<close>) and disjunction (\<open>\<or>\<close>).\<close>

text \<open>Numerical value of a @{type bool}ean.\<close>

definition valOfBool :: "bool \<Rightarrow> nat" where
"valOfBool p = (if p then 1 else 0)"

text \<open>Order on boolean values induced by @{const valOfBool}.\<close>

definition numOrdBool :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"numOrdBool p q \<longleftrightarrow> (valOfBool p) \<le> (valOfBool q)"

text \<open>We show that the numerical order above is just implication.\<close>

lemma numOrdBool_is_imp [simp]:
"(numOrdBool p q) = (p \<longrightarrow> q)"
apply (unfold numOrdBool_def valOfBool_def)
apply (induct_tac p; induct_tac q)
apply (simp_all)
done

text \<open>Note that \<open>;\<close> is \<open>\<or>\<close> and \<open>|\<close> is \<open>\<and>\<close>.\<close>

interpretation icl_boolean_algebra:
  iclaw "TYPE(bool)" "numOrdBool" "op \<or>" "op \<and>"
apply (unfold_locales)
apply (unfold numOrdBool_is_imp)
apply (auto)
done

subsection \<open>Self-interchanging operators: \<open>+\<close>, \<open>*\<close>, \<open>\<or>\<close>, \<open>\<and>\<close>.\<close>

text \<open>For convenience, we define a locale for self-interchanging operators.\<close>

locale self_iclaw =
  iclaw "type" "op =" "self_op" "self_op"
  for type :: "'a itself" and self_op :: "'a binop"

text \<open>
  We next introduce separate locales to capture associativity, commutativity
  and existence of units for some binary operator. We use a bold circle (\<open>\<^bold>\<circ>\<close>)
  to avoid clashes with Isabelle/HOL's symbol (\<open>\<circ>\<close>) for functional composition.
\<close>

locale associative =
  fixes operator :: "'a binop" (infix "\<^bold>\<circ>" 100)
  assumes assoc: "x \<^bold>\<circ> (y \<^bold>\<circ> z) = (x \<^bold>\<circ> y) \<^bold>\<circ> z"

locale commutative =
  fixes operator :: "'a binop" (infix "\<^bold>\<circ>" 100)
  assumes comm: "x \<^bold>\<circ> y = y \<^bold>\<circ> x"

locale has_unit =
  fixes operator :: "'a binop" (infix "\<^bold>\<circ>" 100)
  fixes unit :: "'a" ("\<^bold>1")
  assumes left_unit [simp]: "\<^bold>1 \<^bold>\<circ> x = x"
  assumes right_unit [simp]: "x \<^bold>\<circ> \<^bold>1 = x"

text \<open>Finally, we can set to prove the laws in the paper.\<close>

lemma assoc_comm_imp_self_iclaw:
"(associative bop \<and> commutative bop) \<Longrightarrow> (self_iclaw bop)"
apply (unfold_locales)
apply (unfold associative_def commutative_def)
apply (clarify)
apply (auto)
done

lemma self_iclaw_and_unit_imp_assoc:
"(self_iclaw bop) \<and> (has_unit bop one) \<Longrightarrow> associative bop"
apply (unfold_locales)
apply (unfold self_iclaw_def iclaw_def iclaw_axioms_def)
apply (clarsimp)
apply (drule_tac x = "x" in spec)
apply (drule_tac x = "one" in spec)
apply (drule_tac x = "y" in spec)
apply (drule_tac x = "z" in spec)
apply (simp add: has_unit_def)
done

lemma self_iclaw_and_unit_imp_comm:
"(self_iclaw bop) \<and> (has_unit bop one) \<Longrightarrow> commutative bop"
apply (unfold_locales)
apply (unfold self_iclaw_def iclaw_def iclaw_axioms_def)
apply (clarsimp)
apply (drule_tac x = "one" in spec)
apply (drule_tac x = "x" in spec)
apply (drule_tac x = "y" in spec)
apply (drule_tac x = "one" in spec)
apply (simp add: has_unit_def)
done

text \<open>Lastly, we prove the self-interchange law for \<open>+\<close>, \<open>*\<close>, \<open>\<or>\<close> and \<open>\<and>\<close>.\<close>

interpretation self_icl_plus:
  self_iclaw "TYPE('a::comm_monoid_add)" "op +"
apply (rule assoc_comm_imp_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (unfold associative_def)
apply (simp add: add.assoc)
-- {* Subgoal 2 *}
apply (unfold commutative_def)
apply (simp add: add.commute)
done

interpretation self_icl_mult:
  self_iclaw "TYPE('a::comm_monoid_mult)" "op *"
apply (rule assoc_comm_imp_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (unfold associative_def)
apply (simp add: mult.assoc)
-- {* Subgoal 2 *}
apply (unfold commutative_def)
apply (simp add: mult.commute)
done

interpretation self_icl_conj:
  self_iclaw "TYPE(bool)" "op \<and>"
apply (rule assoc_comm_imp_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (standard) [1]
apply (blast)
-- {* Subgoal 2 *}
apply (standard) [1]
apply (blast)
done

interpretation self_icl_disj:
  self_iclaw "TYPE(bool)" "op \<or>"
apply (rule assoc_comm_imp_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (standard) [1]
apply (blast)
-- {* Subgoal 2 *}
apply (standard) [1]
apply (blast)
done

subsection \<open>Computer arithmetic: Overflow (\<open>\<top>\<close>).\<close>

text \<open>
  We note that the various necessary types and operators to formalise machine
  calculations are developed in the theories:
  \begin{itemize}
    \item @{theory Strict_Operators};
    \item @{theory Machine_Number};
    \item @{theory Overflow_Monad}; and
    \item @{theory Computer_Arith}.
  \end{itemize}
\<close>

paragraph \<open>Cancellation Laws\<close>

lemma Section_8_cancel_law_1a:
fixes p :: "nat machine_number_ext"
fixes q :: "nat machine_number_ext"
shows "q \<noteq> 0 \<Longrightarrow> p \<le> (p *\<^sub>\<infinity> q) div\<^sub>\<infinity> q"
apply (transfer) -- \<open>Just to quantify free variables!\<close>
apply (overflow_tac)
done

lemma Section_8_cancel_law_1b:
fixes p :: "nat comparith"
fixes q :: "nat comparith"
shows "q \<noteq> 0 \<Longrightarrow> q \<noteq> \<bottom> \<Longrightarrow> p \<le> (p *\<^sub>c q) /\<^sub>c q"
apply (transfer) -- \<open>Just to quantify free variables!\<close>
apply (comparith_tac)
done

lemma Section_8_cancel_law_2a:
fixes p :: "nat option"
fixes q :: "nat option"
shows "(p /\<^sub>? q) *\<^sub>? q \<le> p"
apply (transfer) -- \<open>Just to quantify free variables!\<close>
apply (option_tac)
apply (metis mult.commute split_div_lemma)
done

lemma Section_8_cancel_law_2b:
fixes p :: "nat comparith"
fixes q :: "nat comparith"
shows "q \<noteq> \<top> \<Longrightarrow> (p /\<^sub>c q) *\<^sub>c q \<le> p"
apply (transfer) -- \<open>Just to quantify free variables!\<close>
apply (comparith_tac)
apply (transfer)
apply (clarsimp; safe)
-- {* Subgoal 1 *}
apply (metis mult.commute split_div_lemma)
-- {* Subgoal 2 *}
using div_le_dividend dual_order.trans apply (blast)
-- {* Subgoal 3 *}
apply (metis dual_order.trans mult.commute split_div_lemma)
done

paragraph \<open>Interchange Law\<close>

lemma overflow_times_neq_Value_MN_0:
fixes x :: "nat machine_number_ext"
fixes y :: "nat machine_number_ext"
shows
"x \<noteq> Value MN(0) \<Longrightarrow>
 y \<noteq> Value MN(0) \<Longrightarrow> x *\<^sub>\<infinity> y \<noteq> Value MN(0)"
apply (transfer) -- \<open>Just to quantify free variables!\<close>
apply (overflow_tac)
done

interpretation icl_mult_trunc_div_nat_overflow:
  iclaw "TYPE(nat comparith)" "op \<le>" "op *\<^sub>c" "op /\<^sub>c"
apply (unfold_locales)
apply (option_tac)
apply (simp add: overflow_times_neq_Value_MN_0)
apply (unfold times_overflow_def divide_overflow_def)
apply (thin_tac "r \<noteq> Value MN(0)")
apply (thin_tac "s \<noteq> Value MN(0)")
apply (overflow_tac)
apply (transfer)
apply (clarsimp)
apply (safe)
using icl_mult_trunc_div_nat.interchange_law apply (blast)
using div_le_dividend dual_order.trans apply (blast)
apply (meson dual_order.trans icl_mult_trunc_div_nat.interchange_law)
using div_le_dividend dual_order.trans apply (blast)
done

subsection \<open>Note: Partial operators.\<close>

text \<open>Partial operators are formalised in a separate theory \<open>Partiality\<close>.\<close>

subsection \<open>Sets: union (\<open>\<union>\<close>) and disjoint union (\<open>+\<close>) of sets, ordered by inclusion \<open>\<subseteq>\<close>.\<close>

text \<open>Talk to Tony and Georg about the failed proof below! [TODO]\<close>

interpretation preorder_option_subset:
  iclaw "TYPE('a set option)" "(op \<subseteq>\<^sub>?)" "op \<oplus>\<^sub>?" "op \<union>\<^sub>?"
apply (unfold_locales)
apply (rename_tac p q r s)
apply (option_tac)
apply (auto)
-- {* Cannot be proved unless we change the definition of @{term "op \<subseteq>\<^sub>?"}! *}
oops

text \<open>RE: Disjoint union has a unit \<open>{}\<close>, and so it interchanges with itself.\<close>

interpretation disjoint_union_unit:
  has_unit "op \<oplus>\<^sub>?" "Some {}"
apply (unfold_locales)
apply (option_tac)
apply (option_tac)
done

interpretation self_icl_disjoint_union:
  self_iclaw "TYPE('a set option)" "op \<oplus>\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (auto)
done

text \<open>
  RE: But it is clearly not idempotent: \<open>p \<oplus>\<^sub>? p = p\<close> only when \<open>p = {}\<close> or
  \<open>p = \<bottom>\<close> or \<open>p = \<top>\<close>
\<close>

text \<open>Use the type @{type partial} to prove this also for \<open>\<top>\<close>. [TODO]\<close>

lemma [rule_format]:
"\<forall>p. p \<oplus>\<^sub>? p = p \<longleftrightarrow> (p = \<bottom> \<or> p = Some {})"
apply (option_tac)
done
end