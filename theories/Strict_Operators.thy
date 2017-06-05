(******************************************************************************)
(* Project: The Interchange Law in Application to Concurrent Programming      *)
(* File: Strict_Operators.thy                                                 *)
(* Authors: Frank Zeyda, Tony Hoare and Georg Struth                          *)
(******************************************************************************)

section {* Strict Operators *}

theory Strict_Operators
imports Main Real Option_Monad
begin

text \<open>We encoded undefined values by virtue of the option monad.\<close>

text \<open>Strict (lifted) operators always carry a subsection \<open>_\<^sub>?\<close>.\<close>

subsection {* Equality *}

text \<open>We define a strong notion of equality between undefined values.\<close>

fun lifted_equals :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "=\<^sub>?" 50) where
"Some x =\<^sub>? Some y \<longleftrightarrow> x = y" |
"Some x =\<^sub>? None \<longleftrightarrow> False" |
"None =\<^sub>? Some y \<longleftrightarrow> False" |
"None =\<^sub>? None \<longleftrightarrow> True"

subsection {* Relational Operators *}

text \<open>We also define lifted versions of the comparison operators in a similar way.\<close>

fun lifted_leq :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "\<le>\<^sub>?" 50) where
"Some x \<le>\<^sub>? Some y \<longleftrightarrow> x \<le> y" |
"Some x \<le>\<^sub>? None \<longleftrightarrow> False" |
"None \<le>\<^sub>? Some y \<longleftrightarrow> False" |
"None \<le>\<^sub>? None \<longleftrightarrow> True"

fun lifted_less :: "'a::ord option \<Rightarrow> 'a option \<Rightarrow> bool" (infix "<\<^sub>?" 50) where
"Some x <\<^sub>? Some y \<longleftrightarrow> x < y" |
"Some x <\<^sub>? None \<longleftrightarrow> False" |
"None <\<^sub>? Some y \<longleftrightarrow> False" |
"None <\<^sub>? None \<longleftrightarrow> True"

subsection {* Multiplication and Division *}

text \<open>
  Multiplication and division of (possibly) undefined values are defined by way
  of monadic lifting, using Isabelle/HOL's monad syntax.
\<close>

definition lifted_times ::
  "'a::times option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "*\<^sub>?" 70) where
"x *\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; return (x' * y')}"

definition lifted_divide ::
  "'a::{divide,zero} option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "'/\<^sub>?" 70) where
"x /\<^sub>? y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> 0 then return (x' div y') else \<bottom>}"

text \<open>We configure the above operators to be unfolded by @{method option_tac}.\<close>

declare lifted_times_def [option_monad_ops]
declare lifted_divide_def [option_monad_ops]
end