(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: ICL.thy                                                              *)
(******************************************************************************)
(* LAST REVIEWED: TODO *)

section {* ICL Examples *}

theory ICL_Examples
imports Main Real Strict_Operators Overflow_Monad
begin

declare [[syntax_ambiguity_warning=false]]

text \<open>We are going to use the \<open>|\<close> symbol for parallel composition.\<close>

no_notation (ASCII)
  disj  (infixr "|" 30)

subsection {* Locale Definitions *}

text \<open>
  In this section, we encapsulate the interchange law as an Isabelle locale.
  This gives us an elegant way to formulate conjectures that particular types,
  orderings, and operator pairs fulfill the interchange law. It also aids in
  structuring proofs. We define two locales here:~one to introduce the notion
  of order (which has to be a preorder) and another, extending the former, to
  introduce both operators and interchange law as an assumption.
\<close>

subsubsection {* Locale: @{text preorder} *}

text \<open>
  The underlying relation has to be a preorder. Our definition of preorder is,
  however, deliberately weaker than Isabelle/HOL's definition captured by the
  @{locale ordering} locale. That is, we shall not require the assumption
  @{thm ordering.strict_iff_order}. Moreover, for interpretation we only have
  to provide the @{text "\<le>"} operator in our treatment and not \<open><\<close> as well.
\<close>

locale preorder =
  fixes type :: "'a itself"
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes refl: "x \<^bold>\<le> x"
  assumes trans: "x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> z \<Longrightarrow> x \<^bold>\<le> z"
begin

text \<open>Equivalence of elements is defined in terms of mutual less-or-equals.\<close>

definition equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<equiv>" 50) where
"x \<^bold>\<equiv> y \<longleftrightarrow> x \<^bold>\<le> y \<and> y \<^bold>\<le> x"

text \<open>We prove that \<open>\<equiv>\<close> is indeed an equivalence relation.\<close>

lemma equiv_refl:
"x \<^bold>\<equiv> x"
apply (unfold equiv_def)
apply (clarsimp)
apply (rule local.refl)
done

lemma equiv_sym:
"x \<^bold>\<equiv> y \<Longrightarrow> y \<^bold>\<equiv> x"
apply (unfold equiv_def)
apply (clarsimp)
done

lemma equiv_trans:
"x \<^bold>\<equiv> y \<Longrightarrow> y \<^bold>\<equiv> z \<Longrightarrow> x \<^bold>\<equiv> z"
apply (unfold equiv_def)
apply (clarsimp)
apply (rule conjI)
using local.trans apply (blast)
using local.trans apply (blast)
done

text \<open>The following anti-symmetry law holds by definition of equivalence.\<close>

lemma antisym:
"x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> x \<Longrightarrow> x \<^bold>\<equiv> y"
apply (unfold equiv_def)
apply (clarsimp)
done
end

text \<open>
  Next, we prove several useful interpretations of @{locale preorder}s. Due to
  the structuring mechanism of (sub)locales, we are later able to reuse those
  instantiation proofs i.e.~when interpreting of the \<open>iclaw\<close> locale defined in
  the sequel.
\<close>

interpretation preorder_eq:
  preorder "TYPE('a)" "(op =)"
apply (unfold_locales)
apply (simp_all)
done

interpretation preorder_leq:
  preorder "TYPE('a::preorder)" "(op \<le>)"
apply (unfold_locales)
apply (rule order_refl)
apply (erule order_trans; assumption)
done

interpretation preorder_subset:
  preorder "TYPE('a set)" "(op \<subseteq>)"
apply (unfold_locales)
done

interpretation preorder_option_eq:
  preorder "TYPE('a option)" "(op =\<^sub>?)"
apply (unfold_locales)
apply (option_tac)+
done

interpretation preorder_option_leq:
  preorder "TYPE('a::preorder option)" "(op \<le>\<^sub>?)"
apply (unfold_locales)
apply (option_tac)
apply (option_tac)
using order_trans apply (auto)
done

interpretation preorder_option_subset:
  preorder "TYPE('a set option)" "(op \<subseteq>\<^sub>?)"
apply (unfold_locales)
apply (option_tac)
apply (option_tac)
apply (blast)
done

text \<open>Make the above instantiation lemmas automatic simplifications.\<close>

declare preorder_eq.preorder_axioms [simp]
declare preorder_leq.preorder_axioms [simp]
declare preorder_option_eq.preorder_axioms [simp]
declare preorder_option_leq.preorder_axioms [simp]

subsubsection {* Locale: @{text iclaw} *}

text \<open>
  We are ready now to define the @{text iclaw} locale as an extension of the
  @{text preorder} locale. The interchange law is encapsulated as the single
  assumption of that locale. Instantiations will have to prove this assumption
  and thereby show that the interchange law holds for a particular given type,
  ordering relation, and binary operator pair.
\<close>

locale iclaw = preorder +
  fixes seq_op :: "'a binop" (infixr ";" 110)
  fixes par_op :: "'a binop" (infixr "|" 100)
-- \<open>1. Note: the general shape of the interchange law.\<close>
  assumes interchange_law: "(p | r) ; (q | s) \<^bold>\<le> (p ; q) | (r ; s)"

subsection {* Locale Interpretations *}

text \<open>
  In this section, we prove the various instantiations of the interchange law
  in \textbf{Part 1} of the paper.
\<close>

subsubsection \<open>Arithmetic: addition (\<open>+\<close>) and subtraction (\<open>-\<close>) of numbers.\<close>

text \<open>This is proved for the types @{type int}, @{type rat} and @{type real}.\<close>

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

subsubsection \<open>Arithmetic: multiplication (\<open>x\<close>) and division (\<open>/\<close>).\<close>

text \<open>This is proved for the types @{type rat}, @{type real}, and option types thereof.\<close>

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

text \<open>The @{method option_tac} tactic makes the two proofs below very easy.\<close>

interpretation icl_mult_div_rat_strong:
  iclaw "TYPE(rat option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_mult_div_real_strong:
  iclaw "TYPE(real option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

text \<open>Theorem 1 is true for any @{class field} in general, ...\<close>

lemma Theorem1_field:
fixes p :: "'a::field"
fixes q :: "'a::field"
shows "(p / q) * q = (p * q) / q"
using times_divide_eq_left by (blast)

text \<open>... and @{type rat}ional and @{type real} numbers in particular.\<close>

lemma Theorem1_rat:
fixes p :: "rat"
fixes q :: "rat"
shows "(p / q) * q = (p * q) / q"
apply (rule Theorem1_field)
done

lemma Theorem1_real:
fixes p :: "real"
fixes q :: "real"
shows "(p / q) * q = (p * q) / q"
apply (rule Theorem1_field)
done

subsubsection \<open>Natural numbers: multiplication (\<open>x\<close>) and truncated division (\<open>-:-\<close>)\<close>

text \<open>We note that @{term "x div y"} is used in Isabelle for truncated division.\<close>

text \<open>We first prove the lemma below which is also described in the paper.\<close>

lemma trunc_div_mult_leq:
fixes p :: "nat"
fixes q :: "nat"
-- {* The assumption \<open>q > 0\<close> is not needed because \<open>x div 0 = 0\<close>. *}
shows "(p div q) * q \<le> (p * q) div q"
apply (case_tac "q > 0")
apply (metis div_mult_self_is_m mult.commute split_div_lemma)
apply (simp)
done

text \<open>
  We note that Isabelle/HOL defines \<open>x div 0 = 0\<close>. Hence we can prove the law
  even in HOL's weak treatment of undefinedness, as well as the stronger one.
\<close>

interpretation icl_mult_trunc_div_nat:
  iclaw "TYPE(nat)" "op \<le>" "op *" "op div"
apply (unfold_locales)
apply (case_tac "r = 0"; simp_all)
apply (case_tac "s = 0"; simp_all)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis div_mult_self_is_m mult_le_mono trunc_div_mult_leq)
done

interpretation icl_mult_trunc_div_nat_strong:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis div_mult_self_is_m mult_le_mono trunc_div_mult_leq)
done

subsubsection \<open>Propositional calculus: conjunction (\<open>\<and>\<close>) and implication (\<open>\<Rightarrow>\<close>).\<close>

text \<open>TO: Implication \<open>p \<Rightarrow> q\<close> is defined in the usual way as \<open>\<not>p \<or> q\<close>.\<close>

text \<open>We can easily verify the definition of implication.\<close>

lemma "(p \<longrightarrow> q) \<equiv> (\<not> p \<or> q)"
apply (simp)
done

text \<open>We note that \<open>\<turnstile>\<close> is encoded by object-logic implication (\<open>\<longrightarrow>\<close>).\<close>

definition turnstile :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<turnstile>" 50) where
[iff]: "turnstile p q \<equiv> p \<longrightarrow> q"

interpretation icl_imp_conj:
  iclaw "TYPE(bool)" "op \<longrightarrow>" "op \<and>" "op \<turnstile>"
apply (unfold_locales)
apply (auto)
done

subsubsection \<open>Boolean Algebra: conjunction (\<open>\<and>\<close>) and disjunction (\<open>\<or>\<close>).\<close>

text \<open>Numerical value of a boolean value.\<close>

definition valOfBool :: "bool \<Rightarrow> nat" where
"valOfBool p = (if p then 1 else 0)"

text \<open>Order on boolean values induced by the above.\<close>

definition numOrdBool :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<turnstile>" 50) where
"numOrdBool p q \<longleftrightarrow> (valOfBool p) \<le> (valOfBool q)"

text \<open>We can easily show that the numerical order is just implication.\<close>

lemma numOrdBool_is_imp [simp]:
"(numOrdBool p q) = (p \<longrightarrow> q)"
apply (unfold numOrdBool_def valOfBool_def)
apply (induct_tac p; induct_tac q)
apply (simp_all)
done

text \<open>Note that `@{text ";"}' is disjunction and `@{text "|"}' is conjunction.\<close>

interpretation icl_boolean_algebra:
  iclaw "TYPE(bool)" "numOrdBool" "op \<or>" "op \<and>"
apply (unfold_locales)
apply (unfold numOrdBool_is_imp)
apply (auto)
done

subsubsection \<open>Self-interchanging operators: \<open>+\<close>, \<open>*\<close>, \<open>\<or>\<close>, \<open>\<and>\<close>.\<close>

text \<open>For convenience, we define a locale for self-interchanging operators.\<close>

locale self_iclaw =
  iclaw "type" "op =" "self_op" "self_op"
  for type :: "'a itself" and self_op  :: "'a binop"

text \<open>
  We next introduce (separate) locales to capture associativity, commutativity
  and existence of units for some binary operator. We use a bold circle (\<open>\<^bold>\<circ>\<close>)
  not to clash with the Isabelle/HOL's symbol (\<open>\<circ>\<close>) for functional composition.
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

lemma assoc_comm_imp_self_iclaw:
"(associative bop \<and> commutative bop) \<Longrightarrow> (self_iclaw bop)"
apply (standard)
apply (unfold associative_def commutative_def)
apply (clarify)
apply (auto)
done

lemma self_iclaw_unit_imp_assoc:
"(self_iclaw bop) \<and> (has_unit bop one) \<Longrightarrow> associative bop"
apply (standard)
apply (unfold self_iclaw_def iclaw_def iclaw_axioms_def)
apply (clarsimp)
apply (drule_tac x = "x" in spec)
apply (drule_tac x = "one" in spec)
apply (drule_tac x = "y" in spec)
apply (drule_tac x = "z" in spec)
apply (simp add: has_unit_def)
done

lemma self_iclaw_unit_imp_comm:
"(self_iclaw bop) \<and> (has_unit bop one) \<Longrightarrow> commutative bop"
apply (standard)
apply (unfold self_iclaw_def iclaw_def iclaw_axioms_def)
apply (clarsimp)
apply (drule_tac x = "one" in spec)
apply (drule_tac x = "x" in spec)
apply (drule_tac x = "y" in spec)
apply (drule_tac x = "one" in spec)
apply (simp add: has_unit_def)
done

text \<open>Lastly, we prove the self-interchange law for the four operators.\<close>

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

subsubsection \<open>Computer arithmetic: Overflow (\<open>\<top>\<close>).\<close>

default_sort machine_number

text \<open>
  To encode the outcome of a computer calculation, we firstly introduce a new
  type \<open>'a comparith\<close>. Such is an @{type option} type over the machine number
  type @{typ "'a machine_number_ext"}. The latter is introduced in the theory
  @{theory Overflow_Monad}. The order of nesting indeed ensures that we obtain
  the correct strictness properties with respect to \<open>\<bottom>\<close> and \<open>\<top>\<close>, that is \<open>\<bottom>\<close>
  dominates over \<open>\<top>\<close>.
\<close>

type_synonym 'a comparith = "('a machine_number_ext) option"

text \<open>The definition operators for the @{type comparith} type follows next.\<close>

abbreviation comparith_top :: "'a comparith" ("\<top>") where
"comparith_top \<equiv> Some \<top>"

definition comparith_times ::
  "'a::{times,machine_number} comparith binop" (infixl "*\<^sub>M" 70) where
[option_ops]: "x *\<^sub>M y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (x' [*] y')}"

definition comparith_divide ::
  "'a::{zero,divide,machine_number} comparith binop" (infixl "'/\<^sub>M" 70) where
[option_ops]:
"x /\<^sub>M y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> 0 then return (x' [div] y') else \<bottom>}"

paragraph \<open>Cancellation Laws\<close>

lemma Section_8_cancellation_law1a:
"\<And> (p::nat machine_number_ext) (q::nat machine_number_ext).
  q \<noteq> 0 \<Longrightarrow> p \<le> (p [*] q) [div] q"
apply (overflow_tac)
done

lemma Section_8_cancellation_law1b:
"\<And>(p::nat comparith) (q::nat comparith).
  q \<noteq> 0 \<Longrightarrow> q \<noteq> \<bottom> \<Longrightarrow> p \<le> (p *\<^sub>M q) /\<^sub>M q"
apply (option_tac)
apply (overflow_tac)
done

lemma Section_8_cancellation_law2a:
"\<And>(p::nat option) (q::nat option).
  (p /\<^sub>? q) *\<^sub>? q \<le> p"
apply (option_tac)
apply (metis mult.commute split_div_lemma)
done

lemma Section_8_cancellation_law2b:
"\<And>(p::nat comparith) (q::nat comparith).
  q \<noteq> \<top> \<Longrightarrow> (p /\<^sub>M q) *\<^sub>M q \<le> p"
apply (option_tac)
apply (overflow_tac)
apply (transfer)
apply (clarsimp; safe)
-- {* Subgoal 1 *}
apply (metis mult.commute split_div_lemma)
-- {* Subgoal 2 *}
using div_le_dividend dual_order.trans apply (blast)
-- {* Subgoal 3 *}
apply (erule contrapos_np)
apply (clarsimp)
apply (metis dual_order.trans mult.commute split_div_lemma)
done

paragraph \<open>Interchange Law\<close>

lemma overflow_times_neq_Value_MN_0 [rule_format]:
"\<And>(x::nat machine_number_ext) (y::nat machine_number_ext).
 x \<noteq> Value MN(0) \<Longrightarrow>
 y \<noteq> Value MN(0) \<Longrightarrow> x [*] y \<noteq> Value MN(0)"
apply (overflow_tac)
done

interpretation icl_mult_trunc_div_nat_overflow:
  iclaw "TYPE(nat comparith)" "op \<le>" "op *\<^sub>M" "op /\<^sub>M"
apply (unfold_locales)
apply (option_tac)
apply (simp add: overflow_times_neq_Value_MN_0)
apply (unfold overflow_times_def overflow_divide_def)
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

default_sort type

subsubsection \<open>9. Note: Partial operators.\<close>

text \<open>Partial operators are formalised in a separate theory \<open>Partiality\<close>.\<close>

subsubsection \<open>Sets: union (\<open>\<union>\<close>) and disjoint union (\<open>+\<close>) of sets, ordered by inclusion.\<close>

interpretation preorder_option_subset:
  iclaw "TYPE('a set option)" "(op \<subseteq>\<^sub>?)" "op \<oplus>\<^sub>?" "op \<union>\<^sub>?"
apply (unfold_locales)
apply (rename_tac p q r s)
apply (option_tac)
apply (auto)
-- {* Cannot be proved unless we change the definition of @{term "op \<subseteq>\<^sub>?"}! *}
oops

interpretation disjoint_union_unit:
  has_unit "op \<oplus>\<^sub>?" "Some {}"
apply (unfold_locales)
apply (option_tac)
apply (option_tac)
done

lemma [rule_format]:
"\<forall>p. p = p \<oplus>\<^sub>? p \<longleftrightarrow> (p = \<bottom> \<or> p = Some {})"
apply (option_tac)
done
end