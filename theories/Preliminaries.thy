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

subsection {* Monad Syntax *}

text \<open>We use the constant below for ad hoc overloading to avoid ambiguities.\<close>

consts return :: "'a \<Rightarrow> 'b" ("return")

subsection {* Type Class for Equivalence *}

class equiv = ord +
  fixes equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<cong>" 50)
  assumes equiv_mutual_ord : "x \<cong> y \<longleftrightarrow> x \<le> y \<and> y \<le> x"

lemma equiv_relf:
fixes x :: "'a::{equiv, preorder}"
shows "x \<cong> x"
apply (unfold equiv_mutual_ord)
apply (clarsimp)
done

lemma equiv_sym:
"x \<cong> y \<Longrightarrow> y \<cong> x"
apply (unfold equiv_mutual_ord)
apply (auto)
done

lemma equiv_trans:
fixes x :: "'a::{equiv, preorder}"
fixes y :: "'a::{equiv, preorder}"
fixes z :: "'a::{equiv, preorder}"
shows "x \<cong> y \<Longrightarrow> y \<cong> z \<Longrightarrow> x \<cong> z"
apply (unfold equiv_mutual_ord)
using order_trans by (auto)
end