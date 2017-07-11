(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Partiality.thy                                                       *)
(******************************************************************************)

section {* Partiality *}

theory Partiality
imports Preliminaries
  "~~/src/HOL/Library/Monad_Syntax"
begin

text \<open>Our construction here adds a distinct \<open>\<bottom>\<close> and \<open>\<top>\<close> element to some type.\<close>

subsection {* Type Definition *}

text \<open>We define a datatype \<open>'a partial\<close> to lift values into `extended values'.\<close>

datatype 'a partial =
  Bottom ("\<bottom>") | Value "'a" | Top ("\<top>")

subsection {* Proof Support *}

text \<open>Tactic that facilitates proofs about the @{type partial} type.\<close>

named_theorems partial_ops
  "definitional theorems for operators on the type partial"

lemma partial_split_all:
"(\<forall>x::'a partial. P x) = (P Bottom \<and> P Top \<and> (\<forall>x::'a. P (Value x)))"
apply (safe; simp?)
apply (case_tac x)
apply (simp_all)
done

lemma partial_split_ex:
"(\<exists>x::'a partial. P x) = (P Bottom \<or> P Top \<or> (\<exists>x::'a. P (Value x)))"
apply (safe; simp?)
apply (case_tac x)
apply (simp_all) [3]
apply (auto)
done

lemmas partial_split_laws =
  partial_split_all
  partial_split_ex

method partial_tac = (
  (atomize (full))?,
  (simp add: partial_split_laws partial_ops)?,
  (clarsimp; simp?)?)

subsection {* Monadic Constructors *}

text \<open>We have strictness in both \<open>\<bottom>\<close> and \<open>\<top>\<close>.\<close>

primrec partial_bind ::
  "'a partial \<Rightarrow> ('a \<Rightarrow> 'b partial) \<Rightarrow> 'b partial" where
"partial_bind (Bottom) f = Bottom" |
"partial_bind (Value x) f = f x" |
"partial_bind (Top) f = Top"

adhoc_overloading bind partial_bind

definition partial_return :: "'a  \<Rightarrow> 'a partial" ("return") where
[simp]: "partial_return x = Value x"

subsection {* Lifting Functors *}

fun lift_unop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a partial \<Rightarrow> 'b partial)" where
"lift_unop f Bottom = Bottom" |
"lift_unop f (Value x) = Value (f x)" |
"lift_unop f Top = Top"

fun lift_binop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a partial \<Rightarrow> 'b partial \<Rightarrow> 'c partial)" where
"lift_binop f Bottom Bottom = Bottom" |
"lift_binop f Bottom (Value y) = Bottom" |
"lift_binop f Bottom Top = Bottom" |
"lift_binop f (Value x) Bottom = Bottom" |
"lift_binop f (Value x) (Value y) = Value (f x y)" |
"lift_binop f (Value x) Top = Top" |
"lift_binop f Top Bottom = Bottom" |
"lift_binop f Top (Value y) = Top" |
"lift_binop f Top Top = Top"

subsection {* Ordering Relation *}

primrec partial_ord :: "'a partial \<Rightarrow> nat" where
"partial_ord Bottom = 0" |
"partial_ord (Value x) = 1" |
"partial_ord Top = 2"

instantiation partial :: (ord) ord
begin
fun less_eq_partial :: "'a partial \<Rightarrow> 'a partial \<Rightarrow> bool" where
"(Value x) \<le> (Value y) \<longleftrightarrow> x \<le> y" |
"a \<le> b \<longleftrightarrow> (partial_ord a) \<le> (partial_ord b)"

fun less_partial :: "'a partial \<Rightarrow> 'a partial \<Rightarrow> bool" where
"(Value x) < (Value y) \<longleftrightarrow> x < y" |
"a < b \<longleftrightarrow> (partial_ord a) < (partial_ord b)"
instance ..
end

subsection {* Class Instantiations *}

subsubsection {* Preorder *}

instance partial :: (preorder) preorder
apply (intro_classes)
-- {* Subgoal 1 *}
apply (partial_tac)
apply (rule less_le_not_le)
-- {* Subgoal 2 *}
apply (partial_tac)
-- {* Subgoal 3 *}
apply (partial_tac)
apply (erule order_trans)
apply (assumption)
done

subsubsection {* Partial Order *}

instance partial :: (order) order
apply (intro_classes)
apply (partial_tac)
done

subsubsection {* Linear Order *}

instance partial :: (linorder) linorder
apply (intro_classes)
apply (partial_tac)
done

subsubsection {* Lattice *}

instantiation partial :: (type) bot
begin
definition bot_partial :: "'a partial" where
[partial_ops]: "bot_partial = Bottom"
instance ..
end

instantiation partial :: (type) top
begin
definition top_partial :: "'a partial" where
[partial_ops]: "top_partial = Top"
instance ..
end

notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)

instantiation partial :: (lattice) lattice
begin
fun inf_partial :: "'a partial \<Rightarrow> 'a partial \<Rightarrow> 'a partial" where
"Bottom \<sqinter> Bottom = Bottom" |
"Bottom \<sqinter> (Value y) = Bottom" |
"Bottom \<sqinter> Top = Bottom" |
"(Value x) \<sqinter> Bottom = Bottom" |
"(Value x) \<sqinter> (Value y) = Value (x \<sqinter> y)" |
"(Value x) \<sqinter> Top = (Value x)" |
"Top \<sqinter> Bottom = Bottom" |
"Top \<sqinter> Value y = Value y" |
"Top \<sqinter> Top = Top"

fun sup_partial :: "'a partial \<Rightarrow> 'a partial \<Rightarrow> 'a partial" where
"Bottom \<squnion> Bottom = Bottom" |
"Bottom \<squnion> (Value y) = (Value y)" |
"Bottom \<squnion> Top = Top" |
"(Value x) \<squnion> Bottom = (Value x)" |
"(Value x) \<squnion> (Value y) = Value (x \<squnion> y)" |
"(Value x) \<squnion> Top = Top" |
"Top \<squnion> Bottom = Top" |
"Top \<squnion> (Value y) = Top" |
"Top \<squnion> Top = Top"
instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (partial_tac)
-- {* Subgoal 2 *}
apply (partial_tac)
-- {* Subgoal 3 *}
apply (partial_tac)
-- {* Subgoal 4 *}
apply (partial_tac)
-- {* Subgoal 5 *}
apply (partial_tac)
-- {* Subgoal 6 *}
apply (partial_tac)
done
end

lemma partial_ord_inf_lemma [simp]:
"\<forall>a b. partial_ord (a \<sqinter> b) = min (partial_ord a) (partial_ord b)"
apply (partial_tac)
done

lemma partial_ord_sup_lemma [simp]:
"\<forall>a b. partial_ord (a \<squnion> b) = max (partial_ord a) (partial_ord b)"
apply (partial_tac)
done

subsubsection {* Complete Lattice *}

instantiation partial :: (complete_lattice) complete_lattice
begin
definition Inf_partial :: "'a partial set \<Rightarrow> 'a partial" where
[partial_ops]:
"Inf_partial xs =
  (if Bottom \<in> xs then Bottom else
    let values = {x. Value x \<in> xs} in
      if values = {} then Top else Value (Inf values))"

definition Sup_partial :: "'a partial set \<Rightarrow> 'a partial" where
[partial_ops]:
"Sup_partial xs =
  (if Top \<in> xs then Top else
    let values = {x. Value x \<in> xs} in
      if values = {} then Bottom else Value (Sup values))"
instance
apply (intro_classes)
-- {* Subgoal 1 *}
apply (partial_tac)
apply (simp add: Inf_lower)
-- {* Subgoal 2 *}
apply (partial_tac)
apply (metis Inf_greatest mem_Collect_eq)
-- {* Subgoal 3 *}
apply (partial_tac)
apply (simp add: Sup_upper)
-- {* Subgoal 4 *}
apply (partial_tac)
apply (metis Sup_least mem_Collect_eq)
-- {* Subgoal 5 *}
apply (partial_tac)
-- {* Subgoal 6 *}
apply (partial_tac)
done
end
end