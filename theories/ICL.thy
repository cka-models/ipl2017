(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: ICL.thy                                                              *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* The Interchange Law *}

theory ICL
imports Preliminaries
begin

text \<open>We are going to use the \<open>|\<close> symbol for parallel composition.\<close>

no_notation (ASCII)
  disj  (infixr "|" 30)

subsection {* Locale Definitions *}

text \<open>
  In this section, we encapsulate the interchange law via an Isabelle locale.
  This gives us an elegant way to formulate conjectures that particular types,
  orderings and operator pairs fulfill the interchange law. It also aids us in
  structuring proofs. We define two locales here:~one to introduce the notion
  of order (which has to be a preorder) and another, extending the former, to
  introduce the two operators. The interchange law thus becomes an assumption
  of the second locale.
\<close>

subsubsection {* Locale: \<open>preorder\<close> *}

text \<open>
  The underlying relation has to be a preorder. Our definition of preorder is,
  however, deliberately weaker than Isabelle/HOL's, as encapsulated by its
  @{locale ordering} locale. In particular, we shall not require the caveat
  @{thm ordering.strict_iff_order}. Moreover, interpretations only have to
  provide the \<open>\<le>\<close> operator and not \<open><\<close> as well. We use bold-face symbols to
  distinguish our ordering relations from those of Isabelle's type classes.
\<close>

locale preorder =
  fixes type :: "'a itself"
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 50)
  assumes refl: "x \<^bold>\<le> x"
  assumes trans: "x \<^bold>\<le> y \<Longrightarrow> y \<^bold>\<le> z \<Longrightarrow> x \<^bold>\<le> z"
begin

text \<open>Equivalence \<open>\<^bold>\<equiv>\<close> of elements is defined in terms of mutual \<open>\<^bold>\<le>\<close>.\<close>

definition equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<equiv>" 50) where
"x \<^bold>\<equiv> y \<longleftrightarrow> x \<^bold>\<le> y \<and> y \<^bold>\<le> x"

text \<open>We can easily prove that \<open>\<^bold>\<equiv>\<close> is an equivalence relation.\<close>

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
end

subsubsection {* Locale: \<open>iclaw\<close> *}

text \<open>
  We next define the \<open>iclaw\<close> locale as an extension of the @{locale preorder}
  locale above. The interchange law is encapsulated by the single assumption of
  the locale. Instantiations will have to discharge this assumption and thereby
  show that the interchange law holds for a particular type, ordering relation,
  and binary operator pair.
\<close>

locale iclaw = preorder +
  fixes seq_op :: "'a binop" (infixr ";" 100)
  fixes par_op :: "'a binop" (infixr "|" 100)
  assumes interchange_law: "(p | r) ; (q | s) \<^bold>\<le> (p ; q) | (r ; s)"

subsection {* Interpretations *}

text \<open>
  We lastly prove a few useful interpretations of @{locale preorder}s. Due to
  the structuring mechanism of (sub)locales, we will later on be able to reuse
  these interpretation proofs when interpreting the @{locale iclaw} locale for
  particular operators.
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

subsection {* Proof Support *}

text \<open>We make the above instantiation lemmas automatic simplifications.\<close>

declare preorder_eq.preorder_axioms [simp]
declare preorder_leq.preorder_axioms [simp]
end