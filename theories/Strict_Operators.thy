(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Strict_Operators.thy                                                 *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* Strict Operators *}

theory Strict_Operators
imports Preliminaries Option_Monad ICL
begin

text \<open>All strict operators (on @{type option} types) carry a subscript \<open>_\<^sub>?\<close>.\<close>

subsection {* Equality *}

text \<open>We define a strong notion of equality between undefined values.\<close>

fun equals_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "=\<^sub>?" 50) where
"Some x =\<^sub>? Some y \<longleftrightarrow> x = y" |
"Some x =\<^sub>? None \<longleftrightarrow> False" |
"None =\<^sub>? Some y \<longleftrightarrow> False" |
"None =\<^sub>? None \<longleftrightarrow> True"

text \<open>The above indeed coincides with HOL equality.\<close>

lemma equals_option_is_eq:
"(op =\<^sub>?) = (op =)"
apply (rule ext)+
apply (rename_tac x y)
apply (option_tac)
done

subsection {* Relational Operators *}

text \<open>We also define lifted versions of the default orders \<open>\<le>\<close> and \<open><\<close>.\<close>

fun leq_option :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "\<le>\<^sub>?" 50) where
"Some x \<le>\<^sub>? Some y \<longleftrightarrow> x \<le> y" |
"Some x \<le>\<^sub>? None \<longleftrightarrow> False" |
"None \<le>\<^sub>? Some y \<longleftrightarrow> True" |
"None \<le>\<^sub>? None \<longleftrightarrow> True"

fun less_option :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "<\<^sub>?" 50) where
"Some x <\<^sub>? Some y \<longleftrightarrow> x < y" |
"Some x <\<^sub>? None \<longleftrightarrow> False" |
"None <\<^sub>? Some y \<longleftrightarrow> True" |
"None <\<^sub>? None \<longleftrightarrow> False"

text \<open>Likewise, we can prove these correspond to HOL's default lifted order.\<close>

lemma leq_option_is_less_eq:
"(op \<le>\<^sub>?) = (op \<le>)"
apply (rule ext)+
apply (rename_tac x y)
apply (option_tac)
done

lemma less_option_is_less:
"(op <\<^sub>?) = (op <)"
apply (rule ext)+
apply (rename_tac x y)
apply (option_tac)
done

text \<open>Lastly, we lift subset inclusion into the @{type option} type.\<close>

text \<open>
  From Tony's note, it is not entirely clear to me how to define this operator
  It turns out that \<open>None \<subseteq>\<^sub>? Some y\<close> has to be @{const True} in order to prove
  the ICL example (10). Besides, may the result of \<open>x \<subseteq>\<^sub>? y\<close> be undefined too?
  Or do we always expected a simple @{type bool}ean value when applying lifted
  relational operators? Discuss this with Tony and Georg at a suitable moment.
\<close>

fun subset_option :: "'a set option \<Rightarrow> 'a set option \<Rightarrow> bool" (infix "\<subseteq>\<^sub>?" 50) where
"Some x \<subseteq>\<^sub>? Some y \<longleftrightarrow> x \<subseteq> y" |
"Some x \<subseteq>\<^sub>? None \<longleftrightarrow> (*True*) False" |
"None \<subseteq>\<^sub>? Some y \<longleftrightarrow> (*True*) False" |
"None \<subseteq>\<^sub>? None \<longleftrightarrow> True"

subsection {* Generic Lifting *}

text \<open>We use the constant below for ad hoc overloading to avoid ambiguities.\<close>

consts lift_option :: "'a \<Rightarrow> 'b" ("_\<up>\<^sub>?" [1000] 1000)

definition ulift_option ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a option \<Rightarrow> 'b option)" where
"ulift_option f x = do {x' \<leftarrow> x; return (f x')}"

definition blift_option ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>
   ('a option \<Rightarrow> 'b option \<Rightarrow> 'c option)" where
"blift_option f x y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (f x' y')}"

adhoc_overloading lift_option ulift_option
adhoc_overloading lift_option blift_option

text \<open>Note that we do not add the above operators to @{attribute option_ops}.\<close>

lemma ulift_option_simps [simp]:
"ulift_option f \<bottom> = \<bottom>"
"ulift_option f (Some x) = Some (f x)"
apply (unfold ulift_option_def)
apply (simp_all)
done

lemma blift_option_simps [simp]:
"blift_option f x \<bottom> = \<bottom>"
"blift_option f \<bottom> y = \<bottom>"
"blift_option f (Some x') (Some y') = Some (f x' y')"
apply (unfold blift_option_def)
apply (simp_all)
done

subsection {* Lifted Operators *}

paragraph {* Addition and Subtraction *}

definition plus_option :: "'a::plus option binop" (infixl "+\<^sub>?" 70) where
"(op +\<^sub>?) = (op +)\<up>\<^sub>?"

definition minus_option :: "'a::minus option binop" (infixl "-\<^sub>?" 70) where
"(op -\<^sub>?) = (op -)\<up>\<^sub>?"

paragraph {* Multiplication and Division *}

definition times_option :: "'a::times option binop" (infixl "*\<^sub>?" 70) where
"(op *\<^sub>?) = (op *)\<up>\<^sub>?"

definition divide_option :: "'a::{divide, zero} option binop" (infixl "'/\<^sub>?" 70) where
"x /\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> 0 then return (x' div y') else \<bottom>}"

paragraph {* Union and Disjoint Union *}

definition union_option :: "'a set option binop" (infixl "\<union>\<^sub>?" 70) where
"(op \<union>\<^sub>? ) = (op \<union>)\<up>\<^sub>?"

definition disjoint_union :: "'a set option binop" (infixl "\<oplus>\<^sub>?" 70) where
"x \<oplus>\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; if x' \<inter> y' = {} then return (x' \<union> y') else \<bottom>}"

paragraph {* Proof Support *}

declare plus_option_def [option_ops]
declare minus_option_def [option_ops]
declare times_option_def [option_ops]
declare divide_option_def [option_ops]
declare union_option_def [option_ops]
declare disjoint_union_def [option_ops]

subsection {* ICL Interpretations *}

interpretation preorder_equals_option:
  preorder "TYPE('a option)" "(op =\<^sub>?)"
apply (unfold_locales)
apply (option_tac)+
done

interpretation preorder_leq_option:
  preorder "TYPE('a::preorder option)" "(op \<le>\<^sub>?)"
apply (unfold_locales)
apply (option_tac)
apply (option_tac)
using order_trans apply (auto)
done

interpretation preorder_subset_option:
  preorder "TYPE('a set option)" "(op \<subseteq>\<^sub>?)"
apply (unfold_locales)
apply (option_tac)
apply (option_tac)
apply (auto)
done

text \<open>We make the above interpretation lemmas automatic simplifications.\<close>

declare preorder_equals_option.preorder_axioms [simp]
declare preorder_leq_option.preorder_axioms [simp]
declare preorder_subset_option.preorder_axioms [simp]

subsection {* ICL Lifting Lemmas *}

lemma iclaw_eq_lift_option [simp]:
"iclaw (op =) seq_op par_op \<Longrightarrow>
 iclaw (op =\<^sub>?) seq_op\<up>\<^sub>? par_op\<up>\<^sub>?"
apply (unfold iclaw_def iclaw_axioms_def)
apply (option_tac)
done

lemma preorder_leq_lift_option [simp]:
"preorder (op \<le>::'a::ord relop) \<Longrightarrow>
 preorder (op \<le>\<^sub>?::'a::ord option relop)"
apply (unfold_locales)
apply (option_tac)
apply (meson preorder.refl)
apply (option_tac)
apply (meson preorder.trans)
done

lemma iclaw_leq_lift_option [simp]:
"iclaw (op \<le>) seq_op par_op \<Longrightarrow>
 iclaw (op \<le>\<^sub>?) seq_op\<up>\<^sub>? par_op\<up>\<^sub>?"
apply (unfold iclaw_def iclaw_axioms_def)
apply (option_tac)
done
end