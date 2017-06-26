(******************************************************************************)
(* Project: The Interchange Law in Application to Concurrent Programming      *)
(* File: ICL.thy                                                              *)
(* Authors: Frank Zeyda, Tony Hoare and Georg Struth                          *)
(******************************************************************************)

section {* Examples of Applications *}

theory ICL
imports Main Real Strict_Operators Overflow_Monad
begin

text \<open>We are going to use the \<open>|\<close> symbol for parallel composition.\<close>

no_notation (ASCII)
  disj  (infixr "|" 30)

subsection {* Locale Definitions *}

text \<open>
  In this section, we encapsulate the interchange law as an Isabelle locale.
  This gives us an elegant way to formulate conjectures that particular types,
  orderings, and operator triples fulfill the interchange law. It also aids in
  structuring proofs. We define two locales here:~one to introduce the notion
  of order (which has to be a preorder); and another locale that extends the
  former and introduces both operators for the interchange law to hold.
\<close>

subsubsection {* Locale: @{text preorder} *}

text \<open>
  The underlying relation has to be a preorder. Our definition of preorder
  is, however, deliberately weaker than Isabelle/HOL's definition as per the
  @{locale ordering} locale. This is because we do not require the assumption
  @{text "a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b"}. Moreover, for interpretation we only
  have to provide the @{text "\<le>"} operator in our treatment and not \<open><\<close> also.
\<close>

locale preorder =
  fixes type :: "'a itself"
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes refl: "x \<^bold>\<le> x"
  assumes trans: "x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> z \<Longrightarrow> x \<^bold>\<le> z"
begin

text \<open>Equivalence of elements is defined as mutual less-or-equals.\<close>

definition equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<equiv>" 50) where
"x \<^bold>\<equiv> y \<longleftrightarrow> x \<^bold>\<le> y \<and> y \<^bold>\<le> x"

text \<open>We prove that \<open>\<equiv>\<close> is an equivalence relation.\<close>

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

text \<open>
  Next, we prove several instantiations of @{locale ordering}s used later on.
  Due to the structuring of locales, we will be able to use those lemmas in
  instantiations proofs of the \<open>iclaw\<close> locales which we define in the sequel.
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

text \<open>Make the above instantiation lemmas automatic simplifications.\<close>

declare preorder_eq.preorder_axioms [simp]
declare preorder_leq.preorder_axioms [simp]
declare preorder_option_eq.preorder_axioms [simp]
declare preorder_option_leq.preorder_axioms [simp]

subsubsection {* Locale: @{text iclaw} *}

text \<open>
  We are now able to define the @{text "iclaw"} locale as an extension of the
  @{text "preorder"} locale. The interchange law is encapsulated as the single
  assumption of that locale. Instantiations will have to prove this assumption
  and thereby show that the interchange law holds for the respective type,
  relation and sequence/parallel operator pair.
\<close>

locale iclaw = preorder +
  fixes seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr ";" 110)
  fixes par :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "|" 100)
-- \<open>1. Note: the general shape of the interchange law.\<close>
  assumes interchange_law: "(p | r) ; (q | s) \<^bold>\<le> (p ; q) | (r ; s)"

subsection {* Locale Interpretations *}

text \<open>
  In this section, we prove the various instantiations of the interchange law
  in \textbf{Part 1} of the paper.
\<close>

subsubsection \<open>2. Arithmetic: addition (\<open>+\<close>) and subtraction (\<open>-\<close>) of numbers.\<close>

text \<open>This is proved for the types @{type nat}, @{type int}, @{type rat} and @{type real} below.\<close>

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

subsubsection \<open>3. Arithmetic: multiplication (\<open>x\<close>) and division (\<open>/\<close>).\<close>

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

text \<open>The @{method option_tac} tactic makes the two proofs below very easy!\<close>

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

subsubsection \<open>4. Natural numbers: multiplication (\<open>x\<close>) and truncated division (\<open>-:-\<close>)\<close>

text \<open>We note that the operator \<open>div\<close> is used in Isabelle for truncated division.\<close>

lemma trunc_div_lemma:
fixes p :: "nat"
fixes q :: "nat"
-- {* \<open>assumes "q > 0"\<close> not needed! *}
shows "(p div q)*q \<le> (p*q) div q"
apply (case_tac "q > 0")
apply (metis div_mult_self_is_m mult.commute split_div_lemma)
apply (auto)
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
apply (metis div_mult_self_is_m mult_le_mono trunc_div_lemma)
done

interpretation icl_mult_trunc_div_nat_strong:
  iclaw "TYPE(nat option)" "op \<le>\<^sub>?" "op *\<^sub>?" "op /\<^sub>?"
apply (unfold_locales)
apply (option_tac)
apply (safe, clarsimp?)
apply (subgoal_tac "(p div r) * (q div s) * (r * s) \<le> p * q")
apply (metis div_le_mono div_mult_self_is_m nat_0_less_mult_iff)
apply (unfold semiring_normalization_rules(13))
apply (metis div_mult_self_is_m mult_le_mono trunc_div_lemma)
done

subsubsection \<open>5. Propositional calculus: conjunction (\<open>\<and>\<close>) and implication (\<open>\<Rightarrow>\<close>).\<close>

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

subsubsection \<open>6. Boolean Algebra: conjunction (\<open>\<and>\<close>) and disjunction (\<open>\<or>\<close>).\<close>

text \<open>Numerical value of a boolean and the thereby induced ordering.\<close>

definition valOfBool :: "bool \<Rightarrow> nat" where
"valOfBool p = (if p then 1 else 0)"

definition numOrdBool :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "\<turnstile>" 50) where
"numOrdBool p q \<longleftrightarrow> (valOfBool p) \<le> (valOfBool q)"

text \<open>We can easily show that the numerical order defined above is implication.\<close>

lemma numOrdBool_is_imp [simp]:
"(numOrdBool p q) = (p \<longrightarrow> q)"
apply (unfold numOrdBool_def valOfBool_def)
apply (clarsimp)
done

text \<open>Note that `@{text ";"}' is disjunction and `@{text "|"}' is conjunction.\<close>

interpretation icl_boolean_algebra:
  iclaw "TYPE(bool)" "numOrdBool" "op \<or>" "op \<and>"
apply (unfold_locales)
apply (unfold numOrdBool_is_imp)
apply (auto)
done

subsubsection \<open>7. Self-interchanging operators: \<open>+\<close>, \<open>*\<close>, \<open>\<or>\<close>, \<open>\<and>\<close>.\<close>

text \<open>
  We introduce individual locales to capture associativity, commutativity and
  idempotence of a binary operator.
\<close>

no_notation comp (infixl "\<circ>" 55)

locale assoc =
  fixes operator :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<circ>" 100)
  assumes assoc: "x \<circ> (y \<circ> z) = (x \<circ> y) \<circ> z"

locale comm =
  fixes operator :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<circ>" 100)
  assumes comm: "x \<circ> y = y \<circ> x"

locale unit =
  fixes operator :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<circ>" 100)
  fixes unit :: "'a" ("\<^bold>1")
  assumes left_unit [simp]: "\<^bold>1 \<circ> x = x"
  assumes right_unit [simp]: "x \<circ> \<^bold>1 = x"

declare unit.left_unit [simp]
declare unit.right_unit [simp]

lemma assoc_comm_imp_iclaw:
"(assoc bop \<and> comm bop) \<Longrightarrow> (iclaw (op =) bop bop)"
apply (unfold iclaw_def iclaw_axioms_def)
apply (clarsimp)
apply (unfold assoc_def comm_def iclaw_def)
apply (clarsimp)
done

lemma iclaw_unit_imp_assoc_comm:
"(iclaw (op =) bop bop) \<and> (unit bop one) \<Longrightarrow> (assoc bop \<and> comm bop)"
apply (unfold iclaw_def iclaw_axioms_def)
apply (clarsimp)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (unfold assoc_def)
apply (clarify)
apply (drule_tac x = "x" in spec)
apply (drule_tac x = "one" in spec)
apply (drule_tac x = "y" in spec)
apply (drule_tac x = "z" in spec)
apply (clarsimp)
-- {* Subgoal 1 *}
apply (unfold comm_def)
apply (clarify)
apply (drule_tac x = "one" in spec)
apply (drule_tac x = "x" in spec)
apply (drule_tac x = "y" in spec)
apply (drule_tac x = "one" in spec)
apply (clarsimp)
done

subsubsection \<open>8. Computer arithmetic: Overflow (\<open>\<top>\<close>).\<close>

type_synonym 'a comparith = "('a overflow) option"

declare [[syntax_ambiguity_warning = false]]

definition comparith_times ::
  "'a::{times,linorder} comparith \<Rightarrow> 'a comparith \<Rightarrow> 'a comparith"
    (infixl "*\<^sub>c" 70) where
[option_monad_ops]: "x *\<^sub>c y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (x' [*] y')}"

definition comparith_divide ::
  "'a::{zero,divide,linorder} comparith \<Rightarrow> 'a comparith \<Rightarrow> 'a comparith"
    (infixl "'/\<^sub>c" 70) where
[option_monad_ops]: "x /\<^sub>c y =
  do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> Result 0 then return (x' [div] y') else \<bottom>}"

lemma check_overflow_simps [simp]:
"check_overflow f x \<top> = \<top>"
"check_overflow f \<top> y = \<top>"
apply (unfold check_overflow_def)
apply (case_tac x; simp)
apply (case_tac y; simp)
done

lemma check_overflow_Result:
"check_overflow f (Result x) (Result y) =
  (if (f x y) \<le> max_value then Result (f x y) else \<top>)"
apply (unfold check_overflow_def)
apply (case_tac "(f x y) \<le> max_value")
apply (simp_all)
done

lemma check_overflow_neq_Result_0:
"(x::nat overflow) \<noteq> Result 0 \<Longrightarrow>
 (y::nat overflow) \<noteq> Result 0 \<Longrightarrow>
 (check_overflow op * x y \<noteq> Result 0)"
apply (unfold check_overflow_def)
apply (case_tac x; case_tac y)
apply (simp_all)
done

lemma section_4_cancal_law1:
"p \<le> (p [*] q) [div] q"
apply (unfold overflow_times_def overflow_divide_def)
apply (induct_tac p; induct_tac q)
apply (simp_all)
apply (rename_tac p q)
apply (simp add: check_overflow_Result)
apply (clarsimp)
oops

interpretation icl_mult_trunc_div_nat_overflow:
  iclaw "TYPE(nat comparith)" "op \<le>" "op *\<^sub>c" "op /\<^sub>c"
apply (unfold_locales)
apply (option_tac)
apply (unfold overflow_times_def overflow_divide_def)
apply (simp add: check_overflow_neq_Result_0)
apply (clarify)
apply (thin_tac "r \<noteq> Result 0")
apply (thin_tac "s \<noteq> Result 0")
(* apply (fold overflow_times_def overflow_divide_def) *)
apply (induct_tac p; induct_tac r; induct_tac q; induct_tac s)
apply (simp_all)
apply (rename_tac p r q s)
apply (unfold check_overflow_Result)
apply (case_tac "p div r \<le> max_value"; case_tac "q div s \<le> max_value";
       case_tac "p * q \<le> max_value"; case_tac "r * s \<le> max_value")
apply (simp_all)
apply (unfold check_overflow_Result)
apply (simp_all)
-- {* Subgoal 1 *}
using icl_mult_trunc_div_nat.interchange_law order_trans apply (blast)
-- {* Subgoal 2 *}
apply (erule_tac Q = "\<not> q div s \<le> max_value" in contrapos_pp)
apply (clarsimp)
-- {* We can see that this is not provable if p = 0, r = 1 and s = 1. *}
(* apply (subgoal_tac "p = 0 \<and> r = 1 \<and> s = 1"; clarsimp) *)
apply (subgoal_tac "p \<noteq> 0")
apply (metis div_le_dividend less_le_trans nonzero_mult_div_cancel_left not_le)
defer
-- {* Subgoal 3 *}
apply (erule_tac Q = "\<not> p div r \<le> max_value" in contrapos_pp)
apply (clarsimp)
apply (subgoal_tac "q \<noteq> 0")
apply (metis div_le_dividend dual_order.trans nonzero_mult_div_cancel_right)
defer
-- {* Subgoal 4 *}
apply (metis div_le_dividend mult_zero_right nonzero_mult_div_cancel_right order_trans)
oops

(*
text \<open>
  The bottom element \<open>\<bottom>\<close> is already introduced into the algebra by virtue of
  the option type. So we only have to consider the top element, signifying an
  overflow has occurred. Since operators are likewise strict wrt \<open>\<top>\<close>, we can
  use a nested option type to model overflow. As the battle of the giants is
  resolved in favour of \<open>\<bottom>\<close>, the outer @{const None} corresponds to \<open>\<bottom>\<close> and
  the inner @{const None} (i.e.~@{term "Some None"} to \<open>\<top>\<close>.
\<close>

definition top :: "'a option option" ("\<top>") where
"\<top> = Some \<bottom>"

type_synonym 'a overflow = "'a option option"

text \<open>Lifting has to be redefined...!\<close>

definition overflow_times ::
  "'a::times overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow" (infixl "[*]" 70) where
"x [*] y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (x' *\<^sub>? y')}"

definition overflow_divide ::
  "'a::{divide,zero} overflow \<Rightarrow> 'a overflow \<Rightarrow> 'a overflow" (infixl "'['/]" 70) where
"x [/] y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> Some 0 then return (x' div\<^sub>? y') else \<bottom>}"

text \<open>We configure the above operators to be unfolded by @{method option_tac}.\<close>

declare overflow_times_def [option_monad_ops]
declare overflow_divide_def [option_monad_ops]

interpretation icl_mult_trunc_div_nat_overflow:
  iclaw "TYPE(nat overflow)" "op \<le>\<^sub>?" "op [*]" "op [/]"
apply (unfold_locales)
apply (induct_tac p; induct_tac r; induct_tac q; induct_tac s)
apply (simp_all add: overflow_times_def overflow_divide_def)
apply (rename_tac p r q s)
apply (induct_tac p; induct_tac r; induct_tac q; induct_tac s)
apply (simp_all add: option_monad_ops option_return_def)
apply (rename_tac p r q s)
apply (clarify)
apply (rule icl_mult_trunc_div_nat.interchange_law)
done
*)

subsubsection \<open>9. Note: Partial operators.\<close>

text \<open>
  As already explained and used above, the lifting of total into partial
  operators is achieved with the @{type option} types.
\<close>
end