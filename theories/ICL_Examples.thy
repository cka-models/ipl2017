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

text \<open>We are going to use the `\<open>|\<close>' symbol for parallel composition.\<close>

no_notation (ASCII)
  disj  (infixr "|" 30)

text \<open>Example applications of the interchange law from the article.\<close>

subsection \<open>Arithmetic: addition (\<open>+\<close>) and subtraction (\<open>-\<close>) of numbers.\<close>

text \<open>
  We prove the interchange laws for the HOL types @{type int}, @{type rat} and
  @{type real}, as well as the corresponding @{type option} types of those. We
  note that the law does not hold for type @{type nat}, although a weaker
  version using \<open>\<le>\<close> instead of equality is provable because Isabelle/HOL
  interprets the minus operators as monus on natural numbers.
\<close>

interpretation icl_plus_minus_nat:
  iclaw "TYPE(nat)" "op =" "op -" "op +"
apply (unfold_locales)
apply (linarith?)
oops

interpretation icl_plus_minus_nat:
  iclaw "TYPE(nat)" "op \<le>" "op -" "op +"
apply (unfold_locales)
apply (linarith)
oops

interpretation icl_plus_minus_nat_option:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op -\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_plus_minus_int:
  iclaw "TYPE(int)" "op =" "op -" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation icl_plus_minus_rat:
  iclaw "TYPE(rat)" "op =" "op -" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation icl_plus_minus_real:
  iclaw "TYPE(real)" "op =" "op -" "op +"
apply (unfold_locales)
apply (linarith)
done

text \<open>Corresponding proofs for option types and strict operators.\<close>

interpretation icl_plus_minus_int_option:
  iclaw "TYPE(int option)" "op =\<^sub>?" "op -\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_plus_minus_rat_option:
  iclaw "TYPE(rat option)" "op =\<^sub>?" "op -\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_plus_minus_real_option:
  iclaw "TYPE(real option)" "op =\<^sub>?" "op -\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

subsection \<open>Positive arithmetic: with multiplication (\<open>\<times>\<close>).\<close>

interpretation icl_plus_times_nat:
  iclaw "TYPE(nat)" "op \<le>" "op +" "op *"
apply (unfold_locales)
apply (simp add: distrib_left distrib_right)
done

interpretation icl_plus_times_nat_option:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op +\<^sub>?" "op *\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (simp add: distrib_left distrib_right)
done

interpretation icl_plus_times_nat_option:
  iclaw "TYPE(int)" "op \<le>" "op +" "op *"
apply (unfold_locales)
apply (subgoal_tac "p \<ge> 0 \<and> r \<ge> 0 \<and> q \<ge> 0 \<and> s \<ge> 0")
-- {* Subgoal 1 *}
apply (clarify)
apply (unfold ring_distribs)
apply (unfold sym [OF add.assoc])
apply (simp)
oops

text \<open>
  We note that the law can be proved more generally to hold in any (ordered)
  @{class semiring} in which @{term 0} is the least element. To mechanically
  verify this result, it is useful to introduce a type class that guarantees
  that all elements of a type are positive.
\<close>

class positive = zero + ord +
  assumes zero_least: "0 \<le> x"

interpretation icl_positive_semiring:
  iclaw "TYPE('a::{positive,ordered_semiring})" "op \<le>" "op +" "op *"
apply (unfold_locales)
apply (simp add: distrib_left distrib_right)
apply (metis add.right_neutral add_increasing add_mono order_refl zero_least)
done

text \<open>Clearly, all elements of the type @{type nat} are positive.\<close>

instance nat :: positive
apply (intro_classes)
apply (simp)
done

text \<open>
  For other number types, such as @{type int}eger, @{type rat}ional and
  @{type real} numbers, we introduce a subtype \<open>'a pos\<close> that includes only the
  positive individuals of some type @{typ "'a"}. In order to establish the
  non-emptiness caveat of the type definition, we require that the ordering be
  a @{class preorder}.
\<close>

typedef (overloaded) 'a::"{zero, preorder}" pos = "{x::'a. 0 \<le> x}"
apply (clarsimp)
apply (rule_tac x = "0" in exI)
apply (rule order_refl)
done

setup_lifting type_definition_pos

text \<open>We next lift `\<open>\<le>\<close>', `\<open>0\<close>', `\<open>+\<close>' and `\<open>*\<close>' into the new type @{type pos}.\<close>

instantiation pos :: ("{zero,preorder}") preorder
begin
lift_definition less_eq_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool"
is "op \<le>" .
lift_definition less_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool"
is "op <" .
instance
apply (intro_classes; transfer)
using less_le_not_le apply (blast)
using order_refl apply (blast)
using order_trans apply (blast)
done
end

instantiation pos :: ("{zero,preorder}") zero
begin
lift_definition zero_pos :: "'a pos"
is "0" by (rule order_refl)
instance ..
end

text \<open>
  We note that for the lifting of `\<open>+\<close>' and `\<open>*\<close>', we require closure of those
  operators under positive numbers. Such is, however, provable within ordered
  semi-rings, as we establish later on.
\<close>

class plus_pos_cl = zero + ord + plus +
  assumes plus_pos_closure: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x + y"

class times_pos_cl = zero + ord + times +
  assumes times_pos_closure: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x * y"

instantiation pos :: ("{zero,preorder,plus_pos_cl}") plus
begin
lift_definition plus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
is "op +" by (rule plus_pos_closure)
instance ..
end

instantiation pos :: ("{zero,preorder,times_pos_cl}") times
begin
lift_definition times_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
is "op *" by (rule times_pos_closure)
instance ..
end

text \<open>
  We prove that the above closure property of `\<open>+\<close>' and `\<open>*\<close>' wrt the positive
  individuals holds within any (ordered) semi-ring.
\<close>

subclass (in ordered_semiring) plus_pos_cl
apply (unfold class.plus_pos_cl_def)
using local.add_nonneg_nonneg by (blast)

subclass (in ordered_semiring_0) times_pos_cl
apply (unfold class.times_pos_cl_def)
using local.mult_nonneg_nonneg by (blast)

text \<open>
  Lastly, we prove that subtype @{typ "'a pos"} over some (ordered) semi-ring
  is itself and ordered semi-ring, albeit comprising positive elements only.
  With the earlier interpretation proof, namely for \<open>icl_positive_semiring\<close>,
  this implies that the interchange law holds for positive arithmetic with
  multiplication within any (ordered) semi-ring, including positive rational
  and real numbers.
\<close>

instance pos :: ("{zero, preorder}") positive
apply (intro_classes)
apply (transfer)
apply (assumption)
done

instance pos :: (ordered_semiring_0) ordered_semiring
apply (intro_classes; transfer'; simp?)
apply (simp add: add.assoc)
apply (simp add: add.commute)
apply (simp add: add_left_mono)
apply (simp add: mult.assoc)
apply (simp add: distrib_right)
apply (simp add: distrib_left)
apply (simp add: mult_left_mono)
apply (simp add: mult_right_mono)
done

interpretation icl_plus_times_pos:
  iclaw "TYPE('a::ordered_semiring_0 pos)" "op \<le>" "op +" "op *"
apply (unfold_locales)
done

interpretation icl_plus_times_pos_option:
  iclaw "TYPE('a::ordered_semiring_0 pos option)" "op \<le>\<^sub>?" "op +\<^sub>?" "op *\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (rule icl_positive_semiring.interchange_law)
done

interpretation icl_plus_times_pos_int:
  iclaw "TYPE(int pos)" "op \<le>" "op +" "op *"
apply (unfold_locales)
done

interpretation icl_plus_times_pos_rat:
  iclaw "TYPE(rat pos)" "op \<le>" "op +" "op *"
apply (unfold_locales)
done

interpretation icl_plus_times_pos_real:
  iclaw "TYPE(real pos)" "op \<le>" "op +" "op *"
apply (unfold_locales)
done

interpretation icl_plus_times_pos_int_option:
  iclaw "TYPE(int pos option)" "op \<le>\<^sub>?" "op +\<^sub>?" "op *\<^sub>?"
apply (unfold_locales)
done

interpretation icl_plus_times_pos_rat_option:
  iclaw "TYPE(rat pos option)" "op \<le>\<^sub>?" "op +\<^sub>?" "op *\<^sub>?"
apply (unfold_locales)
done

interpretation icl_plus_times_pos_real_option:
  iclaw "TYPE(real pos option)" "op \<le>\<^sub>?" "op +\<^sub>?" "op *\<^sub>?"
apply (unfold_locales)
done

subsection \<open>Arithmetic: multiplication (\<open>\<times>\<close>) and division (\<open>/\<close>) of numbers.\<close>

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

interpretation icl_mult_div_field:
  iclaw "TYPE('a::field)" "op =" "op *" "op /"
apply (unfold_locales)
apply (simp)
done

interpretation icl_mult_div_rat_option:
  iclaw "TYPE(rat option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation icl_mult_div_real_option:
  iclaw "TYPE(real option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

text \<open>
  Theorem 1 likewise holds for @{type rat}ional and @{type real} numbers and
  option types thereof.
\<close>

lemma Theorem1_rat:
fixes p :: "rat"
fixes q :: "rat"
shows "(p / q) * q = (p * q) / q"
apply (insert icl_mult_div_rat.interchange_law [of p q q 1])
apply (unfold div_by_1 mult_1_right)
apply (assumption)
done

lemma Theorem1_real:
fixes p :: "real"
fixes q :: "real"
shows "(p / q) * q = (p * q) / q"
apply (insert icl_mult_div_real.interchange_law [of p q q 1])
apply (unfold div_by_1 mult_1_right)
apply (assumption)
done

lemma Theorem1_rat_option:
fixes p :: "rat option"
fixes q :: "rat option"
shows "(p /\<^sub>? q) *\<^sub>? q = (p *\<^sub>? q) /\<^sub>? q"
apply (insert icl_mult_div_rat_option.interchange_law [of p q q 1])
apply (unfold div_by_1_option mult_1_right_option)
apply (case_tac p; case_tac q; option_tac)
done

lemma Theorem1_real_option:
fixes p :: "real option"
fixes q :: "real option"
shows "(p /\<^sub>? q) *\<^sub>? q = (p *\<^sub>? q) /\<^sub>? q"
apply (insert icl_mult_div_real_option.interchange_law [of p q q 1])
apply (unfold div_by_1_option mult_1_right_option)
apply (case_tac p; case_tac q; option_tac)
done

text \<open>It also holds, more generally, in any division ring.\<close>

context division_ring
begin
lemma div_mult_exchange:
fixes p :: "'a"
fixes q :: "'a"
shows "(p / q) * q = (p * q) / q"
apply (metis eq_divide_eq mult_eq_0_iff)
done
end

subsection \<open>Positive integers: with truncated division (\<open>\<div>\<close>).\<close>

text \<open>
  By default, @{term "x div y"} is also used for truncated (integer) division
  in Isabelle/HOL. Hence, we first introduce a neat syntax \<open>x \<div> y\<close> consistent
  with our notation in the paper. This is done via @{command abbreviation}.
\<close>

abbreviation trunc_div :: "nat binop" (infixl "\<div>" 70) where
"x \<div> y \<equiv> x div y"

abbreviation trunc_div_option :: "nat option binop" (infixl "\<div>\<^sub>?" 70) where
"x \<div>\<^sub>? y \<equiv> x /\<^sub>? y"

text \<open>
  Since Isabelle/HOL defines \<open>x div 0 = 0\<close>, we can prove the interchange law
  even in HOL's weak treatment of undefinedness, as well as in the strong one.
\<close>

interpretation icl_mult_trunc_div_nat:
  iclaw "TYPE(nat)" "op \<le>" "op *" "op \<div>"
apply (unfold_locales)
apply (case_tac "r = 0"; simp_all)
apply (case_tac "s = 0"; simp_all)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis mult.commute mult_le_mono split_div_lemma)
done

interpretation icl_mult_trunc_div_nat_option:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op *\<^sub>?" "op \<div>\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (rule icl_mult_trunc_div_nat.interchange_law)
done

text \<open>
  With the above, we prove Theorem 2 in the paper, both for natural numbers
  and the option type over naturals.
\<close>

lemma Theorem2:
fixes p :: "nat"
fixes q :: "nat"
shows "(p \<div> q) * q \<le> (p * q) \<div> q"
apply (insert icl_mult_trunc_div_nat.interchange_law [of p q q 1])
apply (unfold div_by_1 mult_1_right)
apply (assumption)
done

lemma Theorem2_option:
fixes p :: "nat option"
fixes q :: "nat option"
shows "(p \<div>\<^sub>? q) *\<^sub>? q \<le> (p *\<^sub>? q) \<div>\<^sub>? q"
apply (insert icl_mult_trunc_div_nat_option.interchange_law [of p q q 1])
apply (unfold div_by_1_option mult_1_right_option)
apply (case_tac p; case_tac q; option_tac)
done

subsection \<open>Propositional calculus: conjunction (\<open>\<and>\<close>) and implication (\<open>\<Rightarrow>\<close>).\<close>

text \<open>RE: Implication \<open>p \<Rightarrow> q\<close> is defined in the usual way as \<open>\<not>p \<or> q\<close>.\<close>

text \<open>We can easily verify the above equivalence in HOL.\<close>

lemma "(p \<longrightarrow> q) \<equiv> (\<not> p \<or> q)"
apply (auto)
done

text \<open>
  This instance of the interchange law cannot be proved by way of interpreting
  the @{locale iclaw} locale because rule implication is not an object-logic
  operator. Nonetheless, we can prove the interchange law as an Isabelle/HOL
  proof rule. We note that Isabelle uses \<open>\<longrightarrow>\<close> for implication and \<open>\<Longrightarrow>\<close> for
  meta-level (rule) implication. To make the theorem look as in the paper, we
  temporarily change the syntax of those operators.
\<close>

notation HOL.implies (infixr "\<Rightarrow>" 25)
notation Pure.imp    (infixr "\<turnstile>" 1)

lemma icl_conj_imp_prop:
"(p \<Rightarrow> q) \<and> (r \<Rightarrow> s) \<turnstile> (p \<and> r) \<Rightarrow> (q \<and> s)"
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

interpretation preorder_numOrdBool:
  preorder "TYPE(bool)" "numOrdBool"
apply (unfold_locales)
apply (unfold numOrdBool_is_imp)
apply (auto)
done

text \<open>Note that \<open>;\<close> is \<open>\<or>\<close> and \<open>|\<close> is \<open>\<and>\<close>.\<close>

interpretation icl_boolean_algebra:
  iclaw "TYPE(bool)" "numOrdBool" "op \<or>" "op \<and>"
apply (unfold_locales)
apply (unfold numOrdBool_is_imp)
apply (auto)
done

text \<open>Theorem 3 once again needs to be formulated as an Isabelle proof rule.\<close>

lemma Theorem3:
"q \<and> s \<turnstile> q \<or> s"
apply (auto)
done

no_notation HOL.implies (infixr "\<Rightarrow>" 25)
no_notation Pure.imp    (infixr "\<turnstile>" 1)

subsection \<open>Self-interchanging operators: \<open>+\<close>, \<open>\<times>\<close>, \<open>\<or>\<close>, \<open>\<and>\<close>.\<close>

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

text \<open>
  We first show that any associative and commuting operator self-interchanges.
\<close>

lemma assoc_comm_self_iclaw:
"(associative bop) \<and> (commutative bop) \<Longrightarrow> (self_iclaw bop)"
apply (unfold_locales)
apply (unfold associative_def commutative_def)
apply (clarify)
apply (auto)
done

text \<open>
  We next show that self-interchanging operators with a unit are associative
  and commute (Theorem 4).
\<close>

lemma Theorem4_assoc:
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

lemma Theorem4_commute:
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
apply (rule assoc_comm_self_iclaw)
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
apply (rule assoc_comm_self_iclaw)
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
apply (rule assoc_comm_self_iclaw)
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
apply (rule assoc_comm_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (standard) [1]
apply (blast)
-- {* Subgoal 2 *}
apply (standard) [1]
apply (blast)
done

text \<open>In addition, we can also show self-interchanging of \<open>+\<^sub>?\<close> and \<open>*\<^sub>?\<close>.\<close>

interpretation self_icl_plus_option:
  self_iclaw "TYPE('a::comm_monoid_add option)" "op +\<^sub>?"
apply (rule assoc_comm_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (unfold associative_def)
apply (option_tac)
apply (simp add: add.assoc)
-- {* Subgoal 2 *}
apply (option_tac)
apply (unfold commutative_def)
apply (option_tac)
apply (simp add: add.commute)
done

interpretation self_icl_mult_option:
  self_iclaw "TYPE('a::comm_monoid_mult option)" "op *\<^sub>?"
apply (rule assoc_comm_self_iclaw)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (unfold associative_def)
apply (option_tac)
apply (simp add: mult.assoc)
-- {* Subgoal 2 *}
apply (unfold commutative_def)
apply (option_tac)
apply (simp add: mult.commute)
done

subsection \<open>Note: Partial operators.\<close>

text \<open>TO: This validates the cancellation law in the algebra of Section 4.\<close>

text \<open>
  Note that the below could even be proved if removing the assumption \<open>0 < q\<close>.
  The reason for this is that in Isabelle/HOL, division by zero is defined to
  be zero. Below we, however, conduct the prove not exploiting that fact.
\<close>

lemma trunc_div_mult_cancel:
fixes p :: "nat"
fixes q :: "nat"
assumes "0 < q"
shows "(p \<div> q) * q \<le> p"
apply (insert Theorem2 [of p q])
apply (erule order_trans)
apply (simp)
done

lemma trunc_div_mult_cancel_option:
fixes p :: "nat option"
fixes q :: "nat option"
shows "(p \<div>\<^sub>? q) *\<^sub>? q \<le> p"
apply (induction p; induction q; option_tac)
apply (rename_tac q p)
apply (erule trunc_div_mult_cancel)
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

subsection \<open>Sets: union (\<open>\<union>\<close>) and disjoint union (\<open>+\<close>) of sets, ordered by inclusion \<open>\<subseteq>\<close>.\<close>

text \<open>Proof of the below relies on @{term "\<bottom> \<subseteq>\<^sub>? A"} for any \<open>A\<close>.\<close>

interpretation preorder_option_subset:
  iclaw "TYPE('a set option)" "(op \<subseteq>\<^sub>?)" "op \<oplus>\<^sub>?" "op \<union>\<^sub>?"
apply (unfold_locales)
apply (rename_tac p q r s)
apply (option_tac)
apply (auto)
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

text \<open>TODO: Use the type @{type partial} to prove this also for \<open>\<top>\<close>.\<close>

lemma [rule_format]:
"\<forall>p. p \<oplus>\<^sub>? p = p \<longleftrightarrow> (p = \<bottom> \<or> p = Some {})"
apply (option_tac)
done

subsection \<open>Note: Variance of operators, covariant (\<open>+\<close>,\<open>\<and>\<close>, \<open>\<or>\<close>) and contravariant (\<open>-\<close>, \<open>\<and>\<close>, \<open>\<Leftarrow>\<close>)\<close>

text \<open>
  We introduce the property of covariance and contravariance via locales.
  For covariance, we have a single locale; and for contravariance, three
  different locales to account for all possible combinations.
\<close>

locale covariant = preorder +
  fixes cov_op :: "'a binop" (infixr "cov" 100)
  assumes cov_rule: "x \<^bold>\<le> x' \<and> y \<^bold>\<le> y' \<Longrightarrow> (x cov y) \<^bold>\<le> (x' cov y')"

text \<open>We consider contravariance in the first, second or both operators.\<close>

locale contravariant = preorder +
  fixes cot_op :: "'a binop" (infixr "cot" 100)
  assumes cot_rule: "x' \<^bold>\<le> x \<and> y' \<^bold>\<le> y \<Longrightarrow> (x cot y) \<^bold>\<le> (x' cot y')"

locale contravariant1 = preorder +
  fixes cot_op :: "'a binop" (infixr "cot" 100)
  assumes cot_rule1: "x' \<^bold>\<le> x \<and> y \<^bold>\<le> y' \<Longrightarrow> (x cot y) \<^bold>\<le> (x' cot y')"

locale contravariant2 = preorder +
  fixes cot_op :: "'a binop" (infixr "cot" 100)
  assumes cot_rule2: "x \<^bold>\<le> x' \<and> y' \<^bold>\<le> y \<Longrightarrow> (x cot y) \<^bold>\<le> (x' cot y')"

text \<open>Note that if the ordering is equality, all operators are covariant.\<close>

interpretation covariant_equality:
  covariant "TYPE('a)" "op =" "f::'a binop"
apply (intro_locales)
apply (unfold covariant_axioms_def)
apply (clarsimp)
done

interpretation contravariant_equality:
  contravariant "TYPE('a)" "op =" "f::'a binop"
apply (intro_locales)
apply (unfold contravariant_axioms_def)
apply (clarsimp)
done

interpretation contravariant1_equality:
  contravariant1 "TYPE('a)" "op =" "f::'a binop"
apply (intro_locales)
apply (unfold contravariant1_axioms_def)
apply (clarsimp)
done

interpretation contravariant2_equality:
  contravariant2 "TYPE('a)" "op =" "f::'a binop"
apply (intro_locales)
apply (unfold contravariant2_axioms_def)
apply (clarsimp)
done

text \<open>
  Below, we prove covariance of \<open>+\<close> for @{type nat}ural, @{type int}eger,
  @{type rat}ional and @{type real} numbers, as well as extensions of those
  types with \<open>\<bottom>\<close>.
\<close>

interpretation covariant_plus_nat:
  covariant "TYPE(nat)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_int:
  covariant "TYPE(int)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_rat:
  covariant "TYPE(rat)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_real:
  covariant "TYPE(real)" "op \<le>" "op +"
apply (unfold_locales)
apply (linarith)
done

interpretation covariant_plus_nat_option:
  covariant "TYPE(nat option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_plus_int_option:
  covariant "TYPE(int option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_plus_rat_option:
  covariant "TYPE(rat option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

interpretation covariant_plus_real_option:
  covariant "TYPE(real option)" "op \<le>\<^sub>?" "op +\<^sub>?"
apply (unfold_locales)
apply (option_tac)
done

text \<open>Covariance of conjunction and disjunction with respect to implication.\<close>

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
  counter examples is where \<open>y' = \<bottom>\<close> in \<open>(x cov y) \<^bold>\<le> (x' cov y')\<close> with all
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
apply (clarify)
apply (subgoal_tac "x div y \<le> x div y'")
apply (erule order_trans)
apply (erule div_le_mono)
apply (rule div_le_mono2)
apply (simp_all)
oops

interpretation contravariant2_rat:
  contravariant2 "TYPE(rat)" "op \<le>" "op /"
apply (unfold_locales)
apply (clarify)
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

text \<open>Contravariance in the second operators holds for reverse implication.\<close>

interpretation contravariant_ref_implies:
  contravariant2 "TYPE(bool)" "op \<longrightarrow>" "op \<longleftarrow>"
apply (unfold_locales)
apply (auto)
done

text \<open>
  Covariance and contravariance with respect to equality is trivial in HOL due
  to Leibniz's law following from the axioms of the HOL kernel.
\<close>

subsection {* Note: Modularity, compositionality, locality, etc. *}

text \<open>
  This proof could  be more involved in requiring inductive reasoning about
  arbitrary languages whose operators are covariant with respect to an order.
  In a deep embedding of a specific language, this would not be difficult to
  show. We will not dig deeper into mechanically proving this property in all
  its generality, as it requires deep embedding of HOL functions, and giving
  a semantics to this (in HOL) I stipulate is beyond expressivity of the type
  system of HOL. An inductive proof would have to proceed at the meta-level.
\<close>

subsection \<open>Strings of characters: catenation (\<open>;\<close>) interleaving (\<open>|\<close>) and empty string (\<open>\<epsilon>\<close>).\<close>

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