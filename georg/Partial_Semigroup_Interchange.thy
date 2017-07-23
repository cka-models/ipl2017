section \<open>Interchange\<close>

theory Partial_Semigroup_Interchange
imports Partial_Semigroups Binary_Modalities
begin

class cancellative_pas = pas + cancellative_partial_semigroup

context cancellative_pas
begin
lemma "D w x \<Longrightarrow> D y z \<Longrightarrow> y \<preceq>\<^sub>R w \<Longrightarrow> z \<preceq>\<^sub>R x \<Longrightarrow> rquot (w \<cdot> x) (y \<cdot> z) = (rquot w y) \<cdot> (rquot x z)"
  by (smt local.add_assoc local.add_assocD_var2 local.add_canc2 local.add_comm local.gR_rel_defined local.rquot_prop)

thm add_canc2

thm add_canc1 rquot_prop

lemma cpas_interchange: "D w x \<Longrightarrow> y \<preceq>\<^sub>R w \<Longrightarrow> z \<preceq>\<^sub>R x \<Longrightarrow> rquot (w \<oplus> x) (y \<oplus> z) = (rquot w y) \<oplus> (rquot x z)"
proof -
  assume d: "D w x"
    and o1: " y \<preceq>\<^sub>R w"
   and o2: "z \<preceq>\<^sub>R x"
  have "w \<oplus> x = ((rquot w y) \<oplus> y) \<oplus> ((rquot x z) \<oplus> z)"
    by (metis add_canc2 add_comm' gR_rel_defined o1 o2)
  hence "w \<oplus> x = (rquot w y) \<oplus> (rquot x z) \<oplus> (y \<oplus> z)"
    by (smt d local.add_assocD local.add_assoc_var local.add_canc2 local.add_comm local.gR_rel_defined o1 o2)
  thus ?thesis
    by (smt d local.add_assocD_var2 local.add_assoc_var local.add_comm local.quotr_unique local.rquot_prop o1 o2)
qed
end

context quantale
begin
lemma bres_canc1: "y \<le> x \<rightarrow> (x \<cdot> y)"
  by (simp add: local.bres_galois_imp)

lemma bres_canc2: "x \<cdot> (x \<rightarrow> z) \<le> z"
  by (simp add: local.bres_galois)

lemma fres_canc1: "x \<le> (x \<cdot> y) \<leftarrow> y"
  using local.fres_galois by blast

lemma fres_canc2: "(z \<leftarrow> y) \<cdot> y \<le> z"
  by (simp add: local.fres_galois)
end

context ab_quantale
begin
lemma quantale_interchange: "(w \<rightarrow> y) \<cdot> (x \<rightarrow> z) \<le> (w \<cdot> x) \<rightarrow> (y \<cdot> z)"
proof -
  have "(w \<cdot> x) \<cdot> (w \<rightarrow> y) \<cdot> (x \<rightarrow> z) = (w \<cdot> (w \<rightarrow> y)) \<cdot> (x \<cdot> (x \<rightarrow> z))"
    by (metis mult_assoc mult_commute)
  also have "... \<le> (y \<cdot> z)"
    using local.bres_canc2 local.mult_isol local.mult_isor local.order.trans by blast
  finally show ?thesis
    by (simp add: local.bres_galois_imp mult_assoc)
qed

lemma "(w \<rightarrow> y) \<cdot> (x \<rightarrow> z) = (w \<cdot> x) \<rightarrow> (y \<cdot> z)"
  nitpick
  oops
end

class res_asg = semigroup_mult +
  fixes preord :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and sbres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes preord_refl: "preord x x"
    and preord_trans: "preord x y \<Longrightarrow> preord y z \<Longrightarrow> preord x z"
    and mult_comm: "x * y = y * x"
    and sbres_galois: "preord (x * y) z \<longleftrightarrow> preord y (sbres x z)"
begin
lemma bres_canc1: "preord y (sbres x (x * y))"
  using local.preord_refl local.sbres_galois by blast

lemma bres_canc2: "preord (x * (sbres x z)) z"
  by (simp add: local.preord_refl local.sbres_galois)

lemma mult_iso: "preord x y \<Longrightarrow> preord (z * x) (z * y)"
  using local.bres_canc1 local.preord_trans local.sbres_galois by blast

lemma res_asg_interchange: "preord ((sbres w y) * (sbres x z)) (sbres (w * x) (y * z))"
  by (smt bres_canc1 bres_canc2 mult.semigroup_axioms mult_comm preord_trans sbres_galois semigroup.assoc)
end

class res_asg_test = monoid_mult +
  fixes preord :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and sbres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes preord_refl: "preord x x"
    and preord_trans: "preord x y \<Longrightarrow> preord y z \<Longrightarrow> preord x z"
    and preord_antisym: "preord x y \<Longrightarrow> preord y x"
    and mult_comm: "x * y = y * x"
    and mult_iso: "preord x y \<Longrightarrow> preord (z * x) (z * y)"
    and "preord ((sbres w y) * (sbres x z)) (sbres (w * x) (y * z))"
begin
lemma sbres_galois: "preord (x * y) z \<longleftrightarrow> preord y (sbres x z)"
  nitpick
  oops
end
end