(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Preliminaries.thy                                                    *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* Preliminaries *}

theory Preliminaries
imports Main Real Eisbach
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Type Synonyms *}

text \<open>Type synonym for homogeneous relational operators on a type @{typ "'a"}.\<close>

type_synonym 'a relop = "'a \<Rightarrow> 'a \<Rightarrow> bool"

text \<open>Type synonym for homogeneous unary operators on a type @{typ "'a"}.\<close>

type_synonym 'a unop = "'a \<Rightarrow> 'a"

text \<open>Type synonym for homogeneous binary operators on a type @{typ "'a"}.\<close>

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

subsection {* Lattice Syntax *}

text \<open>We use the constants below for ad hoc overloading to avoid ambiguities.\<close>

consts global_bot :: "'a" ("\<bottom>")
consts global_top :: "'a" ("\<top>")

text \<open>Declaration of global notations for lattice operators.\<close>

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65)

notation
  Inf ("\<Sqinter>") and
  Sup ("\<Squnion>")

subsection {* Reverse Implication *}

abbreviation (input) rimplies :: "[bool, bool] \<Rightarrow> bool" (infixr "\<longleftarrow>" 25)
where "Q \<longleftarrow> P \<equiv> P \<longrightarrow> Q"

subsection {* Monad Syntax *}

text \<open>We use the constant below for ad hoc overloading to avoid ambiguities.\<close>

consts return :: "'a \<Rightarrow> 'b" ("return")

subsection {* Equivalence Operator *}

text \<open>Equivalence is introduced by extending the type class @{class ord}.\<close>

definition (in ord) equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<cong>" 50) where
[iff]: "x \<cong> y \<longleftrightarrow> x \<le> y \<and> y \<le> x"

context preorder
begin
lemma equiv_relf:
"x \<cong> x"
apply (clarsimp)
done

lemma equiv_sym:
"x \<cong> y \<Longrightarrow> y \<cong> x"
apply (clarsimp)
done

lemma equiv_trans:
"x \<cong> y \<Longrightarrow> y \<cong> z \<Longrightarrow> x \<cong> z"
apply (safe)
apply (erule order_trans; assumption)
apply (erule order_trans; assumption)
done
end
end