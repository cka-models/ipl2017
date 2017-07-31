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

text \<open>We are going to use the \<open>|\<close> symbol for parallel composition.\<close>

no_notation (ASCII)
  disj  (infixr "|" 30)

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

subsection \<open>Note: Variance of operators, covariant (\<open>+\<close>,\<open>\<and>\<close>, \<open>\<or>\<close>) and contravariant (\<open>-\<close>, \<open>\<and>\<close>, \<open>\<Leftarrow>\<close>)\<close>

text \<open>
  We introduce the properties of covariance and contravariance via two locales.
  The underlying ordering has to be a @{locale preorder} in both cases.
\<close>

locale covariant = preorder +
  fixes cov_op :: "'a binop" (infixr "cov" 100)
  assumes covariant: "x \<^bold>\<le> x' \<Longrightarrow> y \<^bold>\<le> y' \<Longrightarrow> (x cov y) \<^bold>\<le> (x' cov y')"

text \<open>We consider contravariance in the first, second or both operators.\<close>

locale contravariant = preorder +
  fixes ctv_op :: "'a binop" (infixr "ctv" 100)
  assumes contravariant: "x' \<^bold>\<le> x \<Longrightarrow> y' \<^bold>\<le> y \<Longrightarrow> (x ctv y) \<^bold>\<le> (x' ctv y')"

locale contravariant1 = preorder +
  fixes ctv_op :: "'a binop" (infixr "ctv" 100)
  assumes contravariant: "x' \<^bold>\<le> x \<Longrightarrow> y \<^bold>\<le> y' \<Longrightarrow> (x ctv y) \<^bold>\<le> (x' ctv y')"

locale contravariant2 = preorder +
  fixes ctv_op :: "'a binop" (infixr "ctv" 100)
  assumes contravariant: "x \<^bold>\<le> x' \<Longrightarrow> y' \<^bold>\<le> y \<Longrightarrow> (x ctv y) \<^bold>\<le> (x' ctv y')"

text \<open>
  We prove covariance of \<open>+\<close> for @{type nat}ural, @{type int}eger,
  @{type rat}ional and @{type real} numbers, as well as extensions of those
  types incorporating undefined results.
\<close>

interpretation covariant_plus_nat:
  covariant "TYPE(nat)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_nat_option:
  covariant "TYPE(nat option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_plus_int:
  covariant "TYPE(int)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_int_option:
  covariant "TYPE(int option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_plus_rat:
  covariant "TYPE(rat)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_rat_option:
  covariant "TYPE(rat option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_plus_real:
  covariant "TYPE(real)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_real_option:
  covariant "TYPE(real option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_conj:
  covariant "TYPE(bool)" "op \<longrightarrow>" "op \<and>"
apply (unfold_locales)
apply (clarsimp)
done

interpretation covariant_disj:
  covariant "TYPE(bool)" "op \<longrightarrow>" "op \<or>"
apply (unfold_locales)
apply (clarsimp)
done

text \<open>
  We prove contravariance in the right operator of \<open>-\<close> for @{type nat}ural,
  @{type int}eger, @{type rat}ional and @{type real} numbers. We note that
  contravariance does not hold for their respective @{type option} types. A
  counter examples is where \<open>y' = \<bottom>\<close> in \<open>(x ctv y) \<^bold>\<le> (x' ctv y')\<close> with all
  other quantities defined.
\<close>

interpretation contravariant2_minus_nat:
  contravariant2 "TYPE(nat)" "op \<le>" "op -"
apply (unfold_locales)
apply (linarith)
done

interpretation contravariant2_minus_int:
  contravariant2 "TYPE(int)" "op \<le>" "op -"
apply (unfold_locales)
apply (linarith)
done

interpretation contravariant2_minus_rat:
  contravariant2 "TYPE(rat)" "op \<le>" "op -"
apply (unfold_locales)
apply (linarith)
done

interpretation contravariant2_minus_real:
  contravariant2 "TYPE(real)" "op \<le>" "op -"
apply (unfold_locales)
apply (linarith)
done

text \<open>
  Contravariance of division actually could not be proved. First of all it
  does not hold for plain number types @{type nat} since the additional caveat
  @{term "y' > 0"} is needed, see the proof below. For @{type int}, @{type rat}
  and @{type real} it is even worse, since we also need to show that \<open>y*y'\<close> is
  positive. Moving to @{type option} types does not help as we are facing the
  same issue as for \<open>-\<close> above. Various instances of the contravariance law for
  division may only be proved if we strengthen the assumptions on \<open>y\<close> and \<open>y'\<close>.
\<close>

interpretation contravariant2_nat:
  contravariant2 "TYPE(nat)" "op \<le>" "op div"
apply (unfold_locales)
apply (subgoal_tac "x div y \<le> x div y'")
apply (erule order_trans)
apply (erule div_le_mono)
apply (rule div_le_mono2)
apply (simp_all)
oops

interpretation contravariant2_rat:
  contravariant2 "TYPE(rat)" "op \<le>" "op /"
apply (unfold_locales)
apply (subgoal_tac "x / y \<le> x / y'")
apply (erule order_trans)
apply (erule divide_right_mono) defer
apply (erule divide_left_mono) defer
defer
oops

interpretation contravariant2_div_nat:
  contravariant2 "TYPE(nat option)" "op \<le>\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (safe; clarsimp?) defer
apply (subgoal_tac "x div y \<le> x div y'")
apply (erule order_trans)
apply (erule div_le_mono)
apply (erule div_le_mono2)
apply (assumption)
oops

interpretation contravariant_ref_implies:
  contravariant2 "TYPE(bool)" "op \<longrightarrow>" "op \<longleftarrow>"
apply (unfold_locales)
apply (auto)
done

text \<open>
  Covariance and contravariance with respect to equality is trivial in HOL due
  to Leibniz's law following from the axioms of the HOL kernel.
\<close>

subsection {* Note: Modularity, compositionality, locality, etc.*}

text \<open>
  This proof could  be more involved in requiring inductive reasoning about
  arbitrary languages whose operators are covariant with respect to an order.
  In a deep embedding of a specific language, this would not be difficult to
  show. We will not dig deeper into mechanically proving this property in all
  its generality, as it requires deep embedding of HOL functions, and giving
  a semantics to this (in HOL) I stipulate is beyond expressivity of the type
  system of HOL. An inductive proof would have to proceed at the meta-level.
\<close>

subsection \<open>Strings of characters: catenation (\<open>;\<close>) interleaving \<open>|\<close> and empty string (\<open>\<epsilon>\<close>).\<close>

text \<open>We first define a datatype to formalise the syntax of our string algebra.\<close>

text \<open>Note that we added a constructor for a single character (\<open>atom\<close>).\<close>

datatype 'a str_calc =
  empty_str ("\<epsilon>") |
  atom "'a" |
  seq_str "'a str_calc" "'a str_calc" (infixr ";" 110) |
  par_str "'a str_calc" "'a str_calc" (infixr "|" 100)

text \<open>The following function facilitates construction from HOL strings.\<close>

primrec mk_str :: "string \<Rightarrow> char str_calc" (*("\<guillemotleft>_\<guillemotright>" )*) where
"mk_str [] = \<epsilon>" |
"mk_str (h # t) = seq_str (atom h) (mk_str t)"

syntax "_mk_str" :: "id \<Rightarrow> char str_calc" ("\<guillemotleft>_\<guillemotright>")

parse_translation \<open>
  let
    fun mk_str_tr [Free  (name, _)] = @{const mk_str} $ (HOLogic.mk_string name)
      | mk_str_tr [Const (name, _)] = @{const mk_str} $ (HOLogic.mk_string name)
      | mk_str_tr _ = raise Match;
  in
    [(@{syntax_const "_mk_str"}, K mk_str_tr)]
  end
\<close>

translations "_mk_str s" \<leftharpoondown> "(CONST mk_str) s"

text \<open>The function \<open>ch\<close> yields all characters in a @{type str_calc} term.\<close>

primrec ch :: "'a str_calc \<Rightarrow> 'a set" where
"ch \<epsilon> = {}" |
"ch (atom c) = {c}" |
"ch (p ; q) = (ch p) \<union> (ch q)" |
"ch (p | q) = (ch p) \<union> (ch q)"

text \<open>The function \<open>sd\<close> computes the sequential dependencies using \<open>ch\<close>.\<close>

primrec sd :: "'a str_calc \<Rightarrow> ('a \<times> 'a) set" where
"sd \<epsilon> = {}" |
"sd (atom c) = {}" |
"sd (p ; q) = {(c, d). c \<in> (ch p) \<and> d \<in> (ch q)} \<union> sd(p) \<union> sd(q)" |
"sd (p | q) = sd(p) \<union> sd(q)"

(*<*)
value "ch \<guillemotleft>frank\<guillemotright>"
value "sd \<guillemotleft>frank\<guillemotright>"
(*>*)
text \<open>We are now able to define our ordering of @{type str_calc} objects.\<close>

instantiation str_calc :: (type) ord
begin
definition less_eq_str_calc :: "'a str_calc \<Rightarrow> 'a str_calc \<Rightarrow> bool" where
"less_eq_str_calc p q \<longleftrightarrow> (*ch p = ch q \<and>*)sd(q) \<subseteq> sd(p)"
definition less_str_calc :: "'a str_calc \<Rightarrow> 'a str_calc \<Rightarrow> bool" where
"less_str_calc p q \<longleftrightarrow> (*ch p = ch q \<and>*)sd(q) \<subset> sd(p)"
instance ..
end

text \<open>Proof of the interchange law for the string calculus operators.\<close>

instance str_calc :: (type) preorder
apply (intro_classes)
apply (unfold less_eq_str_calc_def less_str_calc_def)
apply (auto)
done

interpretation preorder_str_calc:
  preorder "TYPE('a str_calc)" "op \<le>"
apply (rule ICL.preorder_leq.preorder_axioms)
done

interpretation iclaw_str_calc:
  iclaw "TYPE('a str_calc)" "op \<le>" "op ;" "op |"
apply (unfold_locales)
apply (unfold less_eq_str_calc_def less_str_calc_def)
apply (clarsimp)
apply (simp add: subset_iff)
(* apply (auto) *)
done

subsection \<open>Note: Small interchange laws.\<close>

lemma equiv_str_calc:
"s \<cong> t \<longleftrightarrow> (*ch s = ch t \<and>*) sd s = sd t"
apply (clarsimp)
apply (unfold less_eq_str_calc_def)
apply (auto)
done

lemma empty_str_seq_unit:
"\<epsilon> ; s \<cong> s"
"s ; \<epsilon> \<cong> s"
apply (unfold equiv_str_calc)
apply (auto)
done

lemma empty_str_par_unit:
"\<epsilon> | s \<cong> s"
"s | \<epsilon> \<cong> s"
apply (unfold equiv_str_calc)
apply (auto)
done

lemma small_interchange_laws:
"(p | q) ; s \<le> p | (q ; s)"
"p ; (r | s) \<le> (p ; r) | s"
"q ; (r | s) \<le> r | (q ; s)"
"(p | q) ; r \<le> (p ; r) | q"
"p ; s \<le> p | s"
"q ; s \<le> s | q"
apply (unfold less_eq_str_calc_def)
apply (auto)
done

subsection \<open>Note: an example derivation\<close>

text \<open>We first prove several key lemmas.\<close>

lemma seq_str_assoc:
"(s ; t) ; u \<ge> s ; t ; u"
apply (unfold less_eq_str_calc_def)
apply (auto)
done

lemma par_str_assoc:
"(s | t) | u \<ge> s | t | u"
apply (unfold less_eq_str_calc_def)
apply (auto)
done

text \<open>
  The following law does not hold but is needed to remove the \<open>ch\<close>-related
  provisos in the law \<open>seq_str_mono\<close>. Alternatively, we could strengthen the
  definition of the order by additionally requiring @{term "ch p = ch q"}.
\<close>

lemma sd_imp_ch_subset:
"sd s \<subseteq> sd t \<Longrightarrow> ch s \<subseteq> ch t"
apply (induction s; induction t)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
defer
defer
apply (simp)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
apply (simp)
oops

lemma seq_str_mono:
"ch s = ch s' \<Longrightarrow>
 ch t = ch t' \<Longrightarrow>
 s \<ge> s' \<Longrightarrow> t \<ge> t' \<Longrightarrow> (s ; t) \<ge> (s' ; t')"
apply (unfold less_eq_str_calc_def)
apply (auto)
done

lemma par_str_mono:
"s \<ge> s' \<Longrightarrow> t \<ge> t' \<Longrightarrow> (s | t) \<ge> (s' | t')"
apply (unfold less_eq_str_calc_def)
apply (auto)
done

lemma str_calc_step:
fixes LHS :: "'a::preorder"
fixes RHS :: "'a::preorder"
fixes MID :: "'a::preorder"
shows "LHS \<ge> MID \<Longrightarrow> MID \<ge> RHS \<Longrightarrow> LHS \<ge> RHS"
using order_trans by (blast)

lemma example_derivation:
assumes lhs: "LHS = \<guillemotleft>abcd\<guillemotright> | \<guillemotleft>xyzw\<guillemotright>"
assumes rhs: "RHS = \<guillemotleft>xaybzwcd\<guillemotright>"
shows "LHS \<ge> RHS"
apply (unfold lhs rhs)
-- \<open>Step 1\<close>
apply (rule_tac MID = "(\<guillemotleft>a\<guillemotright> ; \<guillemotleft>bcd\<guillemotright>) | (\<guillemotleft>xy\<guillemotright> ; \<guillemotleft>zw\<guillemotright>)" in str_calc_step)
apply (unfold less_eq_str_calc_def; auto) [1]
-- \<open>Step 2\<close>
apply (rule_tac MID = "(\<guillemotleft>a\<guillemotright> | \<guillemotleft>xy\<guillemotright>) ; (\<guillemotleft>bcd\<guillemotright> | \<guillemotleft>zw\<guillemotright>)" in str_calc_step)
apply (rule iclaw_str_calc.interchange_law)
-- \<open>Step 3\<close>
apply (rule_tac MID = "(\<guillemotleft>a\<guillemotright> | \<guillemotleft>x\<guillemotright> ; \<guillemotleft>y\<guillemotright>) ; (\<guillemotleft>b\<guillemotright> ; \<guillemotleft>cd\<guillemotright> | \<guillemotleft>zw\<guillemotright>)" in str_calc_step)
apply (unfold less_eq_str_calc_def; auto) [1]
-- \<open>Step 4\<close>
apply (rule_tac MID = "(\<guillemotleft>a\<guillemotright> | \<guillemotleft>x\<guillemotright>) ; \<guillemotleft>y\<guillemotright> ; (\<guillemotleft>b\<guillemotright> | \<guillemotleft>zw\<guillemotright>) ; \<guillemotleft>cd\<guillemotright>" in str_calc_step)
apply (unfold less_eq_str_calc_def; auto) [1]
(* using seq_str_assoc seq_str_mono
  small_interchange_laws(1)
  small_interchange_laws(4) str_calc_step
apply (blast) *)
-- \<open>Remainder of the proof...\<close>
apply (unfold less_eq_str_calc_def)
apply (auto)
done

lemma example_derivation_auto:
assumes lhs: "LHS = \<guillemotleft>abcd\<guillemotright> | \<guillemotleft>xyzw\<guillemotright>"
assumes rhs: "RHS = \<guillemotleft>xaybzwcd\<guillemotright>"
shows "LHS \<ge> RHS"
apply (unfold lhs rhs)
apply (unfold less_eq_str_calc_def)
apply (auto)
done
end