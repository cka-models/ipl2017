(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Strict_Operators.thy                                                 *)
(******************************************************************************)
(* LAST REVIEWED: 10 July 2017 *)

section {* Strict Operators *}

theory Strict_Operators
imports Preliminaries Option_Monad
begin

text \<open>Strict operators carry a subscript \<open>_\<^sub>?\<close>.\<close>

subsection {* Equality *}

text \<open>We define a strong notion of equality between undefined values.\<close>

fun lifted_equals :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "=\<^sub>?" 50) where
"Some x =\<^sub>? Some y \<longleftrightarrow> x = y" |
"Some x =\<^sub>? None \<longleftrightarrow> False" |
"None =\<^sub>? Some y \<longleftrightarrow> False" |
"None =\<^sub>? None \<longleftrightarrow> True"

subsection {* Relational Operators *}

text \<open>We also define lifted versions of arithmetic comparisons and subset.\<close>

fun lifted_leq :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "\<le>\<^sub>?" 50) where
"Some x \<le>\<^sub>? Some y \<longleftrightarrow> x \<le> y" |
"Some x \<le>\<^sub>? None \<longleftrightarrow> False" |
"None \<le>\<^sub>? Some y \<longleftrightarrow> True" |
"None \<le>\<^sub>? None \<longleftrightarrow> True"

fun lifted_less :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "<\<^sub>?" 50) where
"Some x <\<^sub>? Some y \<longleftrightarrow> x < y" |
"Some x <\<^sub>? None \<longleftrightarrow> False" |
"None <\<^sub>? Some y \<longleftrightarrow> True" |
"None <\<^sub>? None \<longleftrightarrow> False"

text \<open>
  From Tony's note, it is not entirely clear to me how to define the operator
  below. It turns out though that \<open>None \<subseteq>\<^sub>? Some y\<close> must be @{const True} in
  order to prove the ICL example (10). It is also not clear to me whether the
  result of \<open>x \<subseteq>\<^sub>? y\<close> could be undefined or is always expected to be a simple
  value i.e.~of type @{type bool}. Discuss this with Tony at a suitable time.
\<close>

fun lifted_subset :: "'a set option \<Rightarrow> 'a set option \<Rightarrow> bool" (infix "\<subseteq>\<^sub>?" 50) where
"Some x \<subseteq>\<^sub>? Some y \<longleftrightarrow> x \<subseteq> y" |
"Some x \<subseteq>\<^sub>? None \<longleftrightarrow> (*True*) False" |
"None \<subseteq>\<^sub>? Some y \<longleftrightarrow> (*True*) False" |
"None \<subseteq>\<^sub>? None \<longleftrightarrow> True"

text \<open>The above definitions coincide with the default ordering on @{type option}.\<close>

lemma lifted_leq_equiv_option_ord:
"op \<le>\<^sub>? = op \<le>"
apply (rule ext)+
apply (rename_tac x y)
apply (option_tac)
done

lemma lifted_less_equiv_option_ord:
"op <\<^sub>? = op <"
apply (rule ext)+
apply (rename_tac x y)
apply (option_tac)
done

subsection {* Multiplication and Division *}

text \<open>
  Multiplication and division of (possibly) undefined values are defined by way
  of monadic lifting, using Isabelle/HOL's built-in support for monad syntax.
\<close>

definition lifted_times :: "'a::times option binop" (infixl "*\<^sub>?" 70) where
"x *\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (x' * y')}"

definition lifted_divide :: "'a::{divide, zero} option binop" (infixl "'/\<^sub>?" 70) where
"x /\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> 0 then return (x' div y') else \<bottom>}"

subsection {* Union and Disjoint Union *}

text \<open>Ditto for union and disjoint union.\<close>

definition lifted_union :: "'a set option binop" (infixl "\<union>\<^sub>?" 70) where
"x \<union>\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (x' \<union> y')}"

definition disjoint_union :: "'a set option binop" (infixl "\<oplus>\<^sub>?" 70) where
"x \<oplus>\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; if x' \<inter> y' = {} then return (x' \<union> y') else \<bottom>}"

text \<open>We configure the above operators to be unfolded by @{method option_tac}.\<close>

declare lifted_times_def [option_ops]
declare lifted_divide_def [option_ops]
declare lifted_union_def [option_ops]
declare disjoint_union_def [option_ops]
end