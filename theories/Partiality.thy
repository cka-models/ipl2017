(******************************************************************************)
(* Submission: "The Interchange Law: A Principle of Concurrent Programming"   *)
(* Authors: Tony Hoare, Bernard Möller, Georg Struth, and Frank Zeyda         *)
(* File: Partiality.thy                                                       *)
(******************************************************************************)
(* LAST REVIEWED: 11 July 2017 *)

section {* Partiality *}

theory Partiality
imports Preliminaries ICL
begin

subsection {* Type Definition *}

text \<open>We define a datatype \<open>'a partial\<close> that adds a distinct \<open>\<bottom>\<close> and \<open>\<top>\<close> to a type \<open>'a\<close>.\<close>

datatype 'a partial =
  Bot | Value "'a" | Top

text \<open>The notation \<open>\<bottom>\<close> is introduced for the constructor @{const Bot}.\<close>
text \<open>The notation \<open>\<top>\<close> is introduced for the constructor @{const Top}.\<close>

adhoc_overloading global_bot Bot
adhoc_overloading global_top Top

subsection {* Proof Support *}

text \<open>Attribute used to collect definitional laws for operators.\<close>

named_theorems partial_ops "definitional laws for operators on partial values"

text \<open>Tactic that facilitates proofs about @{type partial} values.\<close>

lemma split_partial_all:
"(\<forall>x::'a partial. P x) = (P Bot \<and> P Top \<and> (\<forall>x::'a. P (Value x)))"
apply (safe; simp?)
apply (case_tac x)
apply (simp_all)
done

lemma split_partial_ex:
"(\<exists>x::'a partial. P x) = (P Bot \<or> P Top \<or> (\<exists>x::'a. P (Value x)))"
apply (safe; simp?)
apply (case_tac x)
apply (simp_all) [3]
apply (auto)
done

lemmas split_partial =
  split_partial_all
  split_partial_ex

method partial_tac = (
  (atomize (full))?,
  (simp add: split_partial partial_ops),
  (clarsimp; simp?)?)

subsection {* Monadic Constructors *}

text \<open>Note that we have to ensure strictness in both \<open>\<bottom>\<close> and \<open>\<top>\<close>.\<close>

primrec partial_bind ::
  "'a partial \<Rightarrow> ('a \<Rightarrow> 'b partial) \<Rightarrow> 'b partial" where
"partial_bind Bot f = Bot" |
"partial_bind (Value x) f = f x" |
"partial_bind Top f = Top"

adhoc_overloading bind partial_bind

definition partial_return :: "'a  \<Rightarrow> 'a partial" where
[simp]: "partial_return x = Value x"

adhoc_overloading return partial_return

subsection {* Generic Lifting *}

text \<open>We use the constant below for ad hoc overloading to avoid ambiguities.\<close>

consts lift_partial :: "'a \<Rightarrow> 'b" ("_\<up>\<^sub>p" [1000] 1000)

fun ulift_partial :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a partial \<Rightarrow> 'b partial)" where
"ulift_partial f Bot = Bot" |
"ulift_partial f (Value x) = Value (f x)" |
"ulift_partial f Top = Top"

fun blift_partial ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a partial \<Rightarrow> 'b partial \<Rightarrow> 'c partial)" where
"blift_partial f Bot Bot = Bot" |
"blift_partial f Bot (Value y) = Bot" |
"blift_partial f Bot Top = Bot" | -- \<open>@{const Bot} dominates.\<close>
"blift_partial f (Value x) Bot = Bot" |
"blift_partial f (Value x) (Value y) = Value (f x y)" |
"blift_partial f (Value x) Top = Top" |
"blift_partial f Top Bot = Bot" | -- \<open>@{const Bot} dominates.\<close>
"blift_partial f Top (Value y) = Top" |
"blift_partial f Top Top = Top"

adhoc_overloading lift_partial ulift_partial
adhoc_overloading lift_partial blift_partial

subsection {* Lifted Operators *}

text \<open>What about relational operators? How do we lift those? [TODO]\<close>

paragraph {* Addition and Subtraction *}

definition plus_partial :: "'a::plus partial binop" (infixl "+\<^sub>p" 70) where
"(op +\<^sub>p) = (op +)\<up>\<^sub>p"

definition minus_partial :: "'a::minus partial binop" (infixl "-\<^sub>p" 70) where
"(op -\<^sub>p) = (op -)\<up>\<^sub>p"

paragraph {* Multiplication and Division *}

definition times_partial :: "'a::times partial binop" (infixl "*\<^sub>p" 70) where
"(op *\<^sub>p) = (op *)\<up>\<^sub>p"

definition divide_partial :: "'a::{divide, zero} partial binop" (infixl "'/\<^sub>p" 70) where
"x /\<^sub>p y = do {x' \<leftarrow> x; y' \<leftarrow> y; if y' \<noteq> 0 then return (x' div y') else \<bottom>}"

paragraph {* Union and Disjoint Union *}

definition union_partial :: "'a set partial binop" (infixl "\<union>\<^sub>p" 70) where
"(op \<union>\<^sub>p) = (op \<union>)\<up>\<^sub>p"

definition disjoint_union :: "'a set partial binop" (infixl "\<oplus>\<^sub>p" 70) where
"x \<oplus>\<^sub>p y = do {x' \<leftarrow> x; y' \<leftarrow> y; if x' \<inter> y' = {} then return (x' \<union> y') else \<bottom>}"

paragraph {* Proof Support *}

declare plus_partial_def [partial_ops]
declare minus_partial_def [partial_ops]
declare times_partial_def [partial_ops]
declare divide_partial_def [partial_ops]
declare union_partial_def [partial_ops]
declare disjoint_union_def [partial_ops]

subsection {* Ordering Relation *}

primrec partial_ord :: "'a partial \<Rightarrow> nat" where
"partial_ord Bot = 0" |
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
[partial_ops]: "bot_partial = Bot"
instance ..
end

instantiation partial :: (type) top
begin
definition top_partial :: "'a partial" where
[partial_ops]: "top_partial = Top"
instance ..
end

instantiation partial :: (lattice) lattice
begin
fun inf_partial :: "'a partial \<Rightarrow> 'a partial \<Rightarrow> 'a partial" where
"Bot \<sqinter> Bot = Bot" |
"Bot \<sqinter> (Value y) = Bot" |
"Bot \<sqinter> Top = Bot" |
"(Value x) \<sqinter> Bot = Bot" |
"(Value x) \<sqinter> (Value y) = Value (x \<sqinter> y)" |
"(Value x) \<sqinter> Top = (Value x)" |
"Top \<sqinter> Bot = Bot" |
"Top \<sqinter> Value y = Value y" |
"Top \<sqinter> Top = Top"

fun sup_partial :: "'a partial \<Rightarrow> 'a partial \<Rightarrow> 'a partial" where
"Bot \<squnion> Bot = Bot" |
"Bot \<squnion> (Value y) = (Value y)" |
"Bot \<squnion> Top = Top" |
"(Value x) \<squnion> Bot = (Value x)" |
"(Value x) \<squnion> (Value y) = Value (x \<squnion> y)" |
"(Value x) \<squnion> Top = Top" |
"Top \<squnion> Bot = Top" |
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

text \<open>Validation of the definition of meet and join above.\<close>

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
  (if Bot \<in> xs then Bot else
    let values = {x. Value x \<in> xs} in
      if values = {} then Top else Value (Inf values))"

definition Sup_partial :: "'a partial set \<Rightarrow> 'a partial" where
[partial_ops]:
"Sup_partial xs =
  (if Top \<in> xs then Top else
    let values = {x. Value x \<in> xs} in
      if values = {} then Bot else Value (Sup values))"
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

subsection {* ICL Lifting Lemmas *}

lemma iclaw_eq_lift_partial [simp]:
"iclaw (op =) seq_op par_op \<Longrightarrow>
 iclaw (op =) seq_op\<up>\<^sub>p par_op\<up>\<^sub>p"
apply (unfold iclaw_def iclaw_axioms_def)
apply (partial_tac)
done

lemma preorder_less_eq_lift_partial [simp]:
"preorder (op \<le>::'a::ord relop) \<Longrightarrow>
 preorder (op \<le>::'a::ord partial relop)"
apply (unfold_locales)
apply (partial_tac)
apply (meson preorder.refl)
apply (partial_tac)
apply (meson preorder.trans)
done

lemma iclaw_less_eq_lift_partial [simp]:
"iclaw (op \<le>) seq_op par_op \<Longrightarrow>
 iclaw (op \<le>) seq_op\<up>\<^sub>p par_op\<up>\<^sub>p"
apply (unfold iclaw_def iclaw_axioms_def)
apply (partial_tac)
done
end