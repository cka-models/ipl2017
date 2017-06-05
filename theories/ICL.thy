(******************************************************************************)
(* Project: The Interchange Law in Application to Concurrent Programming      *)
(* File: ICL.thy                                                              *)
(* Authors: Frank Zeyda, Tony Hoare and Georg Struth                          *)
(******************************************************************************)

section {* Examples of Applications *}

theory ICL
imports Main Real Strict_Operators
begin

text \<open>We are going to use the \<open>|\<close> symbol for parallel composition.\<close>

no_notation (ASCII)
  disj  (infixr "|" 30)

subsection {* Locale Definitions *}

text \<open>
  In this section, we encapsulate the interchange law as an Isabelle locale.
  This gives us an elegant way to formulate conjectures that particular types,
  orderings, and operator pairs fulfill the interchange law. It is to some
  extent a design decision.
\<close>

subsubsection {* Locale: @{text preorder} *}

text \<open>
  The underlying relation has to be a pre-order. Our definition of pre-order
  is, however, deliberately weaker than Isabelle/HOL's definition as per the
  @{locale ordering} locale since we do not require the assumption
  @{text "a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b"}. Moreover, for interpretation we only
  have to provide the @{text "\<le>"} operator in our treatment, but not \<open><\<close>.
\<close>

locale preorder =
-- {* The @{text type} locale parameter is for convenience only. *}
  fixes type :: "'a itself"
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes refl: "x \<^bold>\<le> x"
  assumes trans: "x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> z \<Longrightarrow> x \<^bold>\<le> z"
begin

text \<open>Equivalence of elements is defined as mutual less-or-equals.\<close>

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

text \<open>The following anti-symmetry law holds (by definition) as well.\<close>

lemma antisym:
"x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> x \<Longrightarrow> x \<^bold>\<equiv> y"
apply (unfold equiv_def)
apply (clarsimp)
done
end

subsubsection {* Locale: @{text iclaw} *}

text \<open>
  We are now able to define the @{text "iclaw"} locale as an extension of the
  @{text "preorder"} locale. The interchange law is encapsulated as the single
  assumption of that locale. Instantiations will have to prove this assumption
  and thereby show that the interchange law holds for the respective type,
  relation and operator pair.
\<close>

locale iclaw = preorder +
  fixes seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr ";" 110)
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "|" 100)
  assumes interchange_law: "(p | r) ; (q | s) \<^bold>\<le> (p ; q) | (r ; s)"

subsection {* Locale Interpretations *}

text \<open>In this section, we prove the instantiations in \textbf{Part 1} of the paper.\<close>

subsubsection \<open>Arithmetic: addition (+) and subtraction (-) of numbers.\<close>

text \<open>This is proved for the types @{type nat}, @{type int}, @{type rat} and @{type real}.\<close>

interpretation icl_plus_minus_nat:
  iclaw "TYPE(nat)" "op =" "op +" "op -"
apply (unfold_locales)
apply (auto) [2]
apply (linarith?)
oops

interpretation icl_plus_minus_int:
  iclaw "TYPE(int)" "op =" "op +" "op -"
apply (unfold_locales)
apply (auto) [2]
apply (linarith)
done

interpretation icl_plus_minus_rat:
  iclaw "TYPE(rat)" "op =" "op +" "op -"
apply (unfold_locales)
apply (auto) [2]
apply (linarith)
done

interpretation icl_plus_minus_real:
  iclaw "TYPE(real)" "op =" "op +" "op -"
apply (unfold_locales)
apply (auto) [2]
apply (linarith)
done

subsubsection \<open>Arithmetic: multiplication (x) and division (/).\<close>

text \<open>This is proved for the types @{type rat}, @{type real}, and option types thereof.\<close>

interpretation icl_mult_div_rat:
  iclaw "TYPE(rat)" "op =" "op *" "op /"
apply (unfold_locales)
apply (auto)
done

interpretation icl_mult_div_real:
  iclaw "TYPE(real)" "op =" "op *" "op /"
apply (unfold_locales)
apply (auto)
done

text \<open>The @{method option_tac} tactic makes the two proofs below very easy.\<close>

interpretation icl_mult_div_rat_strong:
  iclaw "TYPE(rat option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)+
done

interpretation icl_mult_div_real_strong:
  iclaw "TYPE(real option)" "op =\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)+
done

subsubsection \<open>Natural numbers: multiplication (x) and truncated division (div)\<close>

lemma trunc_div_lemma:
fixes p :: "nat"
fixes q :: "nat"
-- {* \<open>assumes "q > 0"\<close> (not needed!) *}
shows "(p div q)*q \<le> (p*q) div q"
apply (case_tac "q > 0")
apply (metis div_mult_self_is_m mult.commute split_div_lemma)
apply (auto)
done

text \<open>
  We note that Isabelle/HOL defines \<open>x div 0 = 0\<close>. Hence we can prove the law
  even in HOL's weak treatment of undefinedness. The law holds indeed in both
  the weak and strong treatment.
\<close>

interpretation icl_mult_trunc_div_nat:
  iclaw "TYPE(nat)" "op \<le>" "op *" "op div"
apply (unfold_locales)
apply (auto) [2]
apply (case_tac "r = 0"; simp_all)
apply (case_tac "s = 0"; simp_all)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis div_mult_self_is_m mult_le_mono trunc_div_lemma)
done

interpretation icl_mult_trunc_div_nat_strong:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales; option_tac)
apply (safe, clarsimp?)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis div_mult_self_is_m mult_le_mono trunc_div_lemma)
done

subsubsection \<open>Propositional calculus: conjunction (\<open>\<and>\<close>) and implication (\<open>\<Rightarrow>\<close>).\<close>

text \<open>We can easily verify the definition of implication.\<close>

lemma "(p \<longrightarrow> q) \<equiv> (\<not> p \<or> q)"
apply (simp)
done

text \<open>We note that \<open>\<turnstile>\<close> is encoded by object-logic implication \<open>\<longrightarrow>\<close> here.\<close>

interpretation icl_imp_conj:
  iclaw "TYPE(bool)" "op \<longrightarrow>" "op \<and>" "op \<longrightarrow>"
apply (unfold_locales)
apply (auto)
done

subsubsection \<open>Boolean Algebra: conjunction (\<open>\<and>\<close>) and disjunction (\<open>\<or>\<close>).\<close>

text \<open>Numerical value of a boolean and the thus-induced ordering.\<close>

definition valOfBool :: "bool \<Rightarrow> nat" where
"valOfBool p = (if p then 1 else 0)"

definition numOrdBool :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<turnstile>" 50) where
"numOrdBool p q \<longleftrightarrow> (valOfBool p) \<le> (valOfBool q)"

text \<open>We can easily proof that the numerical order defined above is implication.\<close>

lemma numOrdBool_is_imp [simp]:
"(numOrdBool p q) = (p \<longrightarrow> q)"
apply (unfold numOrdBool_def valOfBool_def)
apply (clarsimp)
done

text \<open>Note that `@{text ";"}' is disjunction and `@{text "|"}' is conjunction.\<close>

interpretation icl_boolean_algebra:
  iclaw "TYPE(bool)" "op \<turnstile>" "op \<or>" "op \<and>"
apply (unfold_locales)
apply (unfold numOrdBool_is_imp)
apply (auto)
done
end