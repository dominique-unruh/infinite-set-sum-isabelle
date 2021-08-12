theory Infinite_Sum
  imports
    Infinite_Sum_Misc
    "HOL-Analysis.Elementary_Topology"
    "HOL-Library.Extended_Nonnegative_Real"
begin

subsection\<open>Definition and syntax\<close>

definition infsum_converges :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "infsum_converges f A = (\<exists>x. (sum f \<longlongrightarrow> x) (finite_subsets_at_top A))"

definition infsum :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infsum f A = (if infsum_converges f A then Lim (finite_subsets_at_top A) (sum f) else 0)"

text \<open>The following code for the syntax of \<^const>\<open>infsum\<close> is taken with minor modification
      from Isabelle2021, Infinite_Set_Sum.thy\<close>
syntax
  "_infsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::{comm_monoid_add, t2_space}"
  ("(2\<Sum>\<^sub>\<infinity>_\<in>_./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>\<infinity>i\<in>A. b" \<rightleftharpoons> "CONST infsum (\<lambda>i. b) A"

syntax
  "_uinfsum" :: "pttrn \<Rightarrow> 'b \<Rightarrow> 'b::{comm_monoid_add, t2_space}"
  ("(2\<Sum>\<^sub>\<infinity>_./ _)" [0, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>\<infinity>i. b" \<rightleftharpoons> "CONST infsum (\<lambda>i. b) (CONST UNIV)"

syntax
  "_qinfsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a::{comm_monoid_add, t2_space}"
  ("(2\<Sum>\<^sub>\<infinity>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>\<^sub>\<infinity>x|P. t" \<rightharpoonup> "CONST infsum (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun sum_tr' [Abs (x, Tx, t), Const (\<^const_syntax>\<open>Collect\<close>, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const \<^syntax_const>\<open>_qinfsum\<close> $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | sum_tr' _ = raise Match;
in [(\<^const_syntax>\<open>infsum\<close>, K sum_tr')] end
\<close>

subsection \<open>Properties\<close>

lemma infsum_converges_cong: 
  assumes t1: "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum_converges f A = infsum_converges g A"
proof -
  have "sum f X = sum g X"
    if "finite X" and "X \<subseteq> A" for X
    by (meson subset_eq sum.cong t1 that(2))
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum g x"
    by (simp add: eventually_finite_subsets_at_top_weakI)
  hence  "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) =
         (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)"
    for x
    by (simp add: filterlim_cong)
  thus ?thesis
    by (simp add: infsum_converges_def)
qed

lemma infsum_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum f A = infsum g A"
proof -
  have "sum f X = sum g X"
    if "finite X" and "X \<subseteq> A" for X
    by (meson assms in_mono sum.cong that(2))
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum g x"
    by (rule eventually_finite_subsets_at_top_weakI)
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)" 
    for x
    by (rule tendsto_cong)
  hence "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top A) (sum g)"
    unfolding Topological_Spaces.Lim_def[abs_def]
    by auto
  thus ?thesis
    unfolding infsum_def
    using assms infsum_converges_cong by auto
qed

(* lemma ennreal_Sup:
  assumes "bdd_above A" and nonempty: "A\<noteq>{}"
  shows "ennreal (Sup A) = Sup (ennreal ` A)"
proof (rule Sup_eqI[symmetric])
  fix y assume "y \<in> ennreal ` A" thus "y \<le> ennreal (Sup A)"
    using assms cSup_upper ennreal_leI by auto
next
  fix y assume asm: "\<And>z. z \<in> ennreal ` A \<Longrightarrow> z \<le> y"
  show "ennreal (Sup A) \<le> y"
  proof (cases y)
    case (real r)
    show ?thesis      
      by (metis assms(1) cSup_le_iff ennreal_leI real(1) real(2) asm Sup_least bdd_above_top 
          cSUP_le_iff ennreal_le_iff nonempty)
  next
    case top
    thus ?thesis by auto
  qed
qed *)


lemma infsum_converges_cofin_subset:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsum_converges f A" and [simp]: "finite F"
  shows "infsum_converges f (A-F)"
proof-
  from assms(1) obtain x where lim_f: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding infsum_converges_def by auto
  define F' where "F' = F\<inter>A"
  with assms have "finite F'" and "A-F = A-F'"
    by auto
  have "filtermap ((\<union>)F') (finite_subsets_at_top (A-F))
      \<le> finite_subsets_at_top A"
  proof (rule filter_leI)
    fix P assume "eventually P (finite_subsets_at_top A)"
    then obtain X where [simp]: "finite X" and XA: "X \<subseteq> A" 
      and P: "\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P Y"
      unfolding eventually_finite_subsets_at_top by auto
    define X' where "X' = X-F"
    hence [simp]: "finite X'" and [simp]: "X' \<subseteq> A-F"
      using XA by auto
    hence "finite Y \<and> X' \<subseteq> Y \<and> Y \<subseteq> A - F \<longrightarrow> P (F' \<union> Y)" for Y
      using P XA unfolding X'_def using F'_def \<open>finite F'\<close> by blast
    thus "eventually P (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))"
      unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (rule_tac x=X' in exI, simp)
  qed
  with lim_f have "(sum f \<longlongrightarrow> x) (filtermap ((\<union>)F') (finite_subsets_at_top (A-F)))"
    using tendsto_mono by blast
  have "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    if "((sum f \<circ> (\<union>) F') \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    using that unfolding o_def by auto
  hence "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_compose_filtermap [symmetric]
    by (simp add: \<open>(sum f \<longlongrightarrow> x) (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))\<close> 
        tendsto_compose_filtermap)
  have "\<forall>Y. finite Y \<and> Y \<subseteq> A - F \<longrightarrow> sum f (F' \<union> Y) = sum f F' + sum f Y"
    by (metis Diff_disjoint Int_Diff \<open>A - F = A - F'\<close> \<open>finite F'\<close> inf.orderE sum.union_disjoint)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top (A - F). sum f (F' \<union> x) = sum f F' + sum f x"
    unfolding eventually_finite_subsets_at_top
    using exI [where x = "{}"]
    by (simp add: \<open>\<And>P. P {} \<Longrightarrow> \<exists>x. P x\<close>) 
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))\<close> by fastforce
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> sum f F' + (x-sum f F')) (finite_subsets_at_top (A-F))"
    by simp
  hence "(sum f \<longlongrightarrow> x - sum f F') (finite_subsets_at_top (A-F))"
    using tendsto_add_const_iff by blast    
  thus "infsum_converges f (A - F)"
    unfolding infsum_converges_def by auto
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,t2_space}"
  assumes "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0"
  shows infsum_subset_zero: "infsum f A = infsum f B"
    and infsum_converges_subset_zero: "infsum_converges f A = infsum_converges f B"
proof -
  have convB: "infsum_converges f B" and eq: "infsum f A = infsum f B"
    if convA: "infsum_converges f A" and f0: "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0" for A B
  proof -
    define D where "D = (A-B)"
    define D' where "D' = B-A"

    from convA obtain x where limA: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using infsum_converges_def by blast
    have "sum f X = sum f (X - D)"
      if "finite (X::'a set)"
        and "X \<subseteq> A"
      for X :: "'a set"
      using that f0 D_def by (simp add: subset_iff sum.mono_neutral_cong_right)
    hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum f (x - D)"
      by (rule eventually_finite_subsets_at_top_weakI)
    hence "((\<lambda>F. sum f (F-D)) \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using tendsto_cong [THEN iffD1, rotated] limA by fastforce
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F-D) (finite_subsets_at_top A))"
      by (simp add: filterlim_filtermap)
    have "D \<subseteq> A"
      unfolding D_def by simp
    hence "finite_subsets_at_top (A - D) \<le> filtermap (\<lambda>F. F - D) (finite_subsets_at_top A)"
      by (rule finite_subsets_at_top_minus)
    hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A-D))"
      using tendsto_mono [rotated] 
        \<open>(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F - D) (finite_subsets_at_top A))\<close>
      by blast
    have "A - D \<subseteq> B"
      unfolding D_def by auto
    hence "filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B) \<le> finite_subsets_at_top (A - D)"
      by (rule finite_subsets_at_top_inter [where B = B and A = "A-D"])
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B))"
      using tendsto_mono [rotated] \<open>(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A - D))\<close> by blast
    hence "((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)"
      by (simp add: filterlim_filtermap)
    have "sum f (X \<inter> (A - D)) = sum f X"
      if "finite (X::'a set)"
        and "X \<subseteq> B"
      for X :: "'a set"
    proof (rule sum.mono_neutral_cong)
      show "finite X"
        by (simp add: that(1))
      show "finite (X \<inter> (A - D))"
        by (simp add: that(1))
      show "f i = 0"
        if "i \<in> X - X \<inter> (A - D)"
        for i :: 'a
        using that D_def DiffD2 \<open>X \<subseteq> B\<close> f0 by auto 
      show "f i = 0"
        if "i \<in> X \<inter> (A - D) - X"
        for i :: 'a
        using that
        by auto 
      show "f x = f x"
        if "x \<in> X \<inter> (A - D) \<inter> X"
        for x :: 'a
        by simp
    qed
    hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f (x \<inter> (A - D)) = sum f x"
      by (rule eventually_finite_subsets_at_top_weakI)      
    hence limB: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)"
      using tendsto_cong [THEN iffD1 , rotated]
        \<open>((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)\<close> by blast
    thus "infsum_converges f B"
      unfolding infsum_converges_def by auto
    have "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top B) (sum f)"
      if "infsum_converges f B"
      using that    using limA limB
      using finite_subsets_at_top_neq_bot tendsto_Lim by blast
    thus "infsum f A = infsum f B"
      unfolding infsum_def 
      using convA
      by (simp add: \<open>infsum_converges f B\<close>)
  qed
  with assms show "infsum_converges f A = infsum_converges f B"
    by (metis Un_commute)
  thus "infsum f A = infsum f B"
    using assms convB eq
    by (metis infsum_def)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsum_converges f B" and "infsum_converges f A" and AB: "A \<subseteq> B"
  shows infsum_Diff: "infsum f (B - A) = infsum f B - infsum f A"
    and infsum_converges_Diff: "infsum_converges f (B-A)"
proof -
  define limA limB where "limA = infsum f A" and "limB = infsum f B"
  from assms(1) have limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    unfolding infsum_converges_def infsum_def limB_def
    by (auto simp: tendsto_Lim)
  from assms(2) have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)"
    unfolding infsum_converges_def infsum_def limA_def
    by (auto simp: tendsto_Lim)
  have "((\<lambda>F. sum f (F\<inter>A)) \<longlongrightarrow> limA) (finite_subsets_at_top B)"
  proof (subst asm_rl [of "(\<lambda>F. sum f (F\<inter>A)) = sum f o (\<lambda>F. F\<inter>A)"])
    show "(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)"
      unfolding o_def by auto
    show "((sum f \<circ> (\<lambda>F. F \<inter> A)) \<longlongrightarrow> limA) (finite_subsets_at_top B)"
      unfolding o_def 
      using tendsto_compose_filtermap finite_subsets_at_top_inter[OF AB] limA tendsto_mono
        \<open>(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)\<close> by fastforce
  qed
  with limB have "((\<lambda>F. sum f F - sum f (F\<inter>A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_diff by blast
  have "sum f X - sum f (X \<inter> A) = sum f (X - A)"
    if "finite (X::'a set)"
      and "X \<subseteq> B"
    for X :: "'a set"
    using that by (metis add_diff_cancel_left' sum.Int_Diff)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f x - sum f (x \<inter> A) = sum f (x - A)"
    by (rule eventually_finite_subsets_at_top_weakI)  
  hence "((\<lambda>F. sum f (F-A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>F. sum f F - sum f (F \<inter> A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)\<close> by fastforce
  hence "(sum f \<longlongrightarrow> limB - limA) (filtermap (\<lambda>F. F-A) (finite_subsets_at_top B))"
    by (subst tendsto_compose_filtermap[symmetric], simp add: o_def)
  hence limBA: "(sum f \<longlongrightarrow> limB - limA) (finite_subsets_at_top (B-A))"
    using finite_subsets_at_top_minus[OF AB] by (rule tendsto_mono[rotated])
  thus "infsum_converges f (B-A)"
    unfolding infsum_converges_def by auto
  with limBA show "infsum f (B - A) = limB - limA"
    unfolding infsum_def by (simp add: tendsto_Lim) 
qed

lemma infsum_mono_set:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes fx0: "\<And>x. x\<in>B-A \<Longrightarrow> f x \<ge> 0"
    and "A \<subseteq> B"
    and "infsum_converges f A" (* See infsum_converges_set_mono for why this assumption is needed. *)
    and "infsum_converges f B"
  shows "infsum f B \<ge> infsum f A"
proof -
  define limA limB f' where "limA = infsum f A" and "limB = infsum f B"
    and "f' x = (if x \<in> A then f x else 0)" for x
  have "infsum f A = infsum f' B"
  proof (subst infsum_subset_zero [where f = f' and B = A])
    show "f' x = 0"
      if "x \<in> B - A \<union> (A - B)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsum f A = infsum f' A"
      by (metis f'_def infsum_cong)      
  qed
  hence limA_def': "limA = infsum f' B"
    unfolding limA_def
    by auto
  have convA': "infsum_converges f' B"
  proof (rule infsum_converges_subset_zero [THEN iffD1 , where A1 = A])
    show "f' x = 0"
      if "x \<in> A - B \<union> (B - A)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsum_converges f' A"
      by (simp add: assms(3) f'_def infsum_converges_cong)      
  qed
  from assms have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)" 
    and limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    by (auto simp: limA_def limB_def infsum_converges_def infsum_def tendsto_Lim)
  have limA': "(sum f' \<longlongrightarrow> limA) (finite_subsets_at_top B)"
    using finite_subsets_at_top_neq_bot tendsto_Lim convA'
    unfolding limA_def' infsum_def  infsum_converges_def
    by fastforce 
  have "f' i \<le> f i"
    if "i \<in> X" and "X \<subseteq> B"
    for i :: 'a and X
    unfolding f'_def using fx0 that
    using \<open>X \<subseteq> B\<close> by auto
  hence "sum f' X \<le> sum f X"
    if "finite (X::'a set)"
      and "X \<subseteq> B"
    for X :: "'a set"
    using sum_mono
    by (simp add: sum_mono that(2)) 
  hence sumf'_leq_sumf: "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f' x \<le> sum f x"
    by (rule eventually_finite_subsets_at_top_weakI)
  show "limA \<le> limB"
    using finite_subsets_at_top_neq_bot limB limA' sumf'_leq_sumf 
    by (rule tendsto_le)
qed

lemma infsum_converges_finite[simp]:
  assumes "finite F"
  shows "infsum_converges f F"
  unfolding infsum_converges_def finite_subsets_at_top_finite[OF assms]
  using tendsto_principal_singleton by fastforce 

lemma infsum_finite[simp]:
  assumes "finite F"
  shows "infsum f F = sum f F"
  using assms by (auto intro: tendsto_Lim simp: finite_subsets_at_top_finite infsum_def principal_eq_bot_iff tendsto_principal_singleton)

lemma infsum_approx_sum:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "infsum_converges f A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsum f A) \<le> \<epsilon>"
proof -
  have "infsum_converges f A \<Longrightarrow>
    0 < \<epsilon> \<Longrightarrow> (sum f \<longlongrightarrow> Lim (finite_subsets_at_top A) (sum f)) (finite_subsets_at_top A)"
    unfolding infsum_converges_def
    using finite_subsets_at_top_neq_bot tendsto_Lim by blast
  hence "(sum f \<longlongrightarrow> infsum f A) (finite_subsets_at_top A)"
    unfolding infsum_def
    using assms
    by simp
  hence "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (sum f F) (infsum f A) < \<epsilon>"
    using assms(2) by (rule tendstoD)
  have "finite X \<Longrightarrow>
         X \<subseteq> A \<Longrightarrow>
         \<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) (infsum f A) < \<epsilon> \<Longrightarrow>
         \<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsum f A) \<le> \<epsilon>"
    for X
    by fastforce    
  thus ?thesis
    using eventually_finite_subsets_at_top
    by (metis (no_types, lifting)
        \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. dist (sum f F) (infsum f A) < \<epsilon>\<close>)
qed

lemma norm_infsum_bound:
  fixes f :: "'b \<Rightarrow> 'a::real_normed_vector"
    and A :: "'b set"
  assumes a1: "infsum_converges (\<lambda>x. norm (f x)) A"
  shows "norm (infsum f A) \<le> (infsum (\<lambda>x. norm (f x)) A)"
proof (cases "infsum_converges f A")
  case True
  have "norm (infsum f A) \<le> (infsum (\<lambda>x. norm (f x)) A) + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof-
    have "\<exists>F. norm (infsum f A - sum f F) \<le> \<epsilon> \<and> finite F \<and> F \<subseteq> A"
      using infsum_approx_sum[where A=A and f=f and \<epsilon>="\<epsilon>"] a1 True \<open>0 < \<epsilon>\<close>
      by (metis dist_commute dist_norm)
    then obtain F where "norm (infsum f A - sum f F) \<le> \<epsilon>"
      and "finite F" and "F \<subseteq> A"
      by (simp add: atomize_elim)
    hence "norm (infsum f A) \<le> norm (sum f F) + \<epsilon>"
      by (smt norm_triangle_sub)
    also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) F + \<epsilon>"
      using norm_sum by auto
    also have "\<dots> \<le> (infsum (\<lambda>x. norm (f x)) A) + \<epsilon>"
    proof-
      have "infsum (\<lambda>x. norm (f x)) F \<le> infsum (\<lambda>x. norm (f x)) A"
      proof (rule infsum_mono_set)
        show "0 \<le> norm (f x)"
          if "x \<in> A - F"
          for x :: 'b
          using that
          by simp 
        show "F \<subseteq> A"
          by (simp add: \<open>F \<subseteq> A\<close>)          
        show "infsum_converges (\<lambda>x. norm (f x)) F"
          using \<open>finite F\<close> by auto         
        show "infsum_converges (\<lambda>x. norm (f x)) A"
          by (simp add: assms)          
      qed
      thus ?thesis
        by (simp_all flip: infsum_finite add: \<open>finite F\<close>)
    qed
    finally show ?thesis 
      by assumption
  qed
  thus ?thesis
    using linordered_field_class.field_le_epsilon by blast
next
  case False
  obtain t where t_def: "(sum (\<lambda>x. norm (f x)) \<longlongrightarrow> t) (finite_subsets_at_top A)"
    using a1 unfolding infsum_converges_def by blast
  have sumpos: "sum (\<lambda>x. norm (f x)) X \<ge> 0"
    for X
    by (simp add: sum_nonneg)
  have tgeq0:"t \<ge> 0"
  proof(rule ccontr)
    define S::"real set" where "S = {s. s < 0}"
    assume "\<not> 0 \<le> t"
    hence "t < 0" by simp
    hence "t \<in> S"
      unfolding S_def by blast
    moreover have "open S"
    proof-
      have "closed {s::real. s \<ge> 0}"
        using Elementary_Topology.closed_sequential_limits[where S = "{s::real. s \<ge> 0}"]
        by (metis Lim_bounded2 mem_Collect_eq)
      moreover have "{s::real. s \<ge> 0} = UNIV - S"
        unfolding S_def by auto
      ultimately have "closed (UNIV - S)"
        by simp
      thus ?thesis
        by (simp add: Compl_eq_Diff_UNIV open_closed) 
    qed
    ultimately have "\<forall>\<^sub>F X in finite_subsets_at_top A. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      using t_def unfolding tendsto_def by blast
    hence "\<exists>X. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      by (metis (no_types, lifting) False eventually_mono filterlim_iff infsum_converges_def)
    then obtain X where "(\<Sum>x\<in>X. norm (f x)) \<in> S"
      by blast
    hence "(\<Sum>x\<in>X. norm (f x)) < 0"
      unfolding S_def by auto      
    thus False using sumpos by smt
  qed
  have "\<exists>!h. (sum (\<lambda>x. norm (f x)) \<longlongrightarrow> h) (finite_subsets_at_top A)"
    using t_def finite_subsets_at_top_neq_bot tendsto_unique by blast
  hence "t = (Topological_Spaces.Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))))"
    using t_def unfolding Topological_Spaces.Lim_def
    by (metis the_equality)     
  hence "Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))) \<ge> 0"
    using tgeq0 by blast
  thus ?thesis unfolding infsum_def 
    using False by auto
qed


lemma infsum_tendsto:
  assumes \<open>infsum_converges f S\<close>
  shows \<open>((\<lambda>F. sum f F) \<longlongrightarrow> infsum f S) (finite_subsets_at_top S)\<close>
  by (metis assms finite_subsets_at_top_neq_bot infsum_converges_def infsum_def tendsto_Lim)

lemma infsum_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infsum (\<lambda>_. c) F = of_nat (card F) * c\<close>
  apply (subst infsum_finite[OF assms])
  by simp

lemma infsum_zero[simp]:
  shows \<open>infsum (\<lambda>_. 0) S = 0\<close>
  unfolding infsum_def sum.neutral_const
  by (simp add: tendsto_Lim)

lemma
  fixes f g :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes \<open>infsum_converges f A\<close>
  assumes \<open>infsum_converges g A\<close>
  shows infsum_add: \<open>infsum (\<lambda>x. f x + g x) A = infsum f A + infsum g A\<close>
    and infsum_converges_add: \<open>infsum_converges (\<lambda>x. f x + g x) A\<close>
proof -
  note lim_f = infsum_tendsto[OF assms(1)]
    and lim_g = infsum_tendsto[OF assms(2)]
  then have lim: \<open>(sum (\<lambda>x. f x + g x) \<longlongrightarrow> infsum f A + infsum g A) (finite_subsets_at_top A)\<close>
    unfolding sum.distrib
    by (rule tendsto_add)
  then show conv: \<open>infsum_converges (\<lambda>x. f x + g x) A\<close>
    unfolding infsum_converges_def by auto
  show \<open>infsum (\<lambda>x. f x + g x) A = infsum f A + infsum g A\<close>
    unfolding infsum_def 
    using lim_f lim_g lim
    by (auto simp: assms conv tendsto_Lim)
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes "infsum_converges f A"
  assumes "infsum_converges f B"
  assumes disj: "A \<inter> B = {}"
  shows infsum_Un_disjoint: \<open>infsum f (A \<union> B) = infsum f A + infsum f B\<close>
    and infsum_converges_Un_disjoint: \<open>infsum_converges f (A \<union> B)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 0)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 0)\<close> for x
  have conv_fA: \<open>infsum_converges fA (A \<union> B)\<close>
    unfolding fA_def
    apply (subst infsum_converges_subset_zero, auto)
    by (simp add: assms(1) infsum_converges_cong)
  have conv_fB: \<open>infsum_converges fB (A \<union> B)\<close>
    unfolding fB_def
    apply (subst infsum_converges_subset_zero, auto)
    by (smt (verit, ccfv_SIG) assms(2) assms(3) disjoint_iff infsum_converges_cong)
  have fAB: \<open>f x = fA x + fB x\<close> for x
    unfolding fA_def fB_def by simp
  have \<open>infsum f (A \<union> B) = infsum fA (A \<union> B) + infsum fB (A \<union> B)\<close>
    unfolding fAB
    using conv_fA conv_fB by (rule infsum_add)
  also have \<open>\<dots> = infsum fA A + infsum fB B\<close>
    unfolding fA_def fB_def
    by (subst infsum_subset_zero[where A=\<open>A\<union>B\<close>], auto)+
  also have \<open>\<dots> = infsum f A + infsum f B\<close>
    apply (subst infsum_cong[where f=fA and g=f], simp add: fA_def)
    apply (subst infsum_cong[where f=fB and g=f], simp add: fB_def)
    using disj by auto
  finally show \<open>infsum f (A \<union> B) = infsum f A + infsum f B\<close>
    by -
  from conv_fA conv_fB
  have \<open>infsum_converges (\<lambda>x. fA x + fB x) (A \<union> B)\<close>
    by (rule infsum_converges_add)
  then show \<open>infsum_converges f (A \<union> B)\<close>
    unfolding fAB by -
qed

(* Counterexample:
   Fix a rational-valued f such that f sums to \<pi> on B and to \<pi> + 1 on A (over the reals).
   Consider the following image space: It contains all rationals and all reals \<ge> 4.
   Then f converges on A but not on B.

   Maybe the lemma holds if the image space is complete?
   Or if the image space is a topological vector space?
 *)
(* lemma infsum_converges_set_mono:
  assumes \<open>infsum_converges f A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>infsum_converges f B\<close> *)


lemma infsum_converges_union_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> infsum_converges f (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>infsum_converges f (\<Union>a\<in>A. B a)\<close>
  using finite conv disj apply induction by (auto intro!: infsum_converges_Un_disjoint)

lemma sum_infsum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> infsum_converges f (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>sum (\<lambda>a. infsum f (B a)) A = infsum f (\<Union>a\<in>A. B a)\<close>
  using assms
proof (insert finite conv disj, induction)
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  have \<open>(\<Sum>a\<in>insert x F. infsum f (B a)) = infsum f (B x) + (\<Sum>a\<in>F. infsum f (B a))\<close>
    apply (subst sum.insert) using insert by auto
  also have \<open>\<dots> = infsum f (B x) + infsum f (\<Union> (B ` F))\<close>
    apply (subst insert.IH) using assms insert by auto
  also have \<open>\<dots> = infsum f (B x \<union> \<Union> (B ` F))\<close>
    apply (rule infsum_Un_disjoint[symmetric])
    using insert.prems insert.hyps by (auto simp: infsum_converges_union_disjoint)
  also have \<open>\<dots> = infsum f (\<Union>a\<in>insert x F. B a)\<close>
    by auto
  finally show ?case
    by -
qed

theorem infsum_mono:
  fixes f g :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}" (* Does it also hold in order_topology? *)
  assumes "infsum_converges f A"
    and "infsum_converges g A"
  assumes leq: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows "infsum f A \<le> infsum g A"
proof -
  note limf = infsum_tendsto[OF assms(1)]
    and limg = infsum_tendsto[OF assms(2)]
  have sum_leq: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> sum g F\<close>
    by (simp add: in_mono leq sum_mono)
  show ?thesis
    using _ limg limf apply (rule tendsto_le)
    by (auto intro!: sum_leq)
qed

subsection \<open>Infinite sum over specific monoids\<close>

lemma infsum_converges_ennreal[simp]: \<open>infsum_converges (f::_ \<Rightarrow> ennreal) S\<close>
proof -
  define B where \<open>B = (SUP F\<in>{F. F \<subseteq> S \<and> finite F}. sum f F)\<close>

  have upper: \<open>\<forall>\<^sub>F F in finite_subsets_at_top S. sum f F \<le> B\<close>
    apply (rule eventually_finite_subsets_at_top_weakI)
    unfolding B_def
    by (simp add: SUP_upper)
  have lower: \<open>\<forall>\<^sub>F n in finite_subsets_at_top S. x < sum f n\<close> if \<open>x < B\<close> for x
  proof -
    obtain F where Fx: \<open>sum f F > x\<close> and \<open>F \<subseteq> S\<close> and \<open>finite F\<close>
      using \<open>x < B\<close> unfolding B_def
      by (metis (mono_tags, lifting)  less_SUP_iff mem_Collect_eq)
    have geq: \<open>sum f Y \<ge> sum f F\<close> if \<open>finite Y\<close> and \<open>Y \<supseteq> F\<close> for Y
      by (simp add: sum_mono2 that(1) that(2))
    show ?thesis
      unfolding eventually_finite_subsets_at_top
      apply (rule exI[of _ F])
      using \<open>finite F\<close> \<open>F \<subseteq> S\<close> Fx geq by force
  qed
  
  show ?thesis
    unfolding infsum_converges_def
    apply (rule exI[of _ B])
    using upper lower by (rule increasing_tendsto)
qed

lemma infsum_superconst_infinite:
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infsum f S = (\<infinity>::ennreal)"
proof -
  have \<open>(sum f \<longlongrightarrow> \<infinity>) (finite_subsets_at_top S)\<close>
  proof (rule order_tendstoI[rotated], simp)
    fix y :: ennreal assume \<open>y < \<infinity>\<close>
    then have \<open>y / b < \<infinity>\<close>
      by (metis b ennreal_divide_eq_top_iff gr_implies_not_zero infinity_ennreal_def top.not_eq_extremum)
    then obtain F where \<open>finite F\<close> and \<open>F \<subseteq> S\<close> and cardF: \<open>card F > y / b\<close>
      using \<open>infinite S\<close>
      by (metis ennreal_Ex_less_of_nat infinite_arbitrarily_large infinity_ennreal_def)
    moreover have \<open>sum f Y > y\<close> if \<open>finite Y\<close> and \<open>F \<subseteq> Y\<close> and \<open>Y \<subseteq> S\<close> for Y
    proof -
      have \<open>y < b * card F\<close>
        by (metis \<open>y < \<infinity>\<close> b cardF divide_less_ennreal ennreal_mult_eq_top_iff gr_implies_not_zero infinity_ennreal_def mult.commute top.not_eq_extremum)
      also have \<open>\<dots> \<le> b * card Y\<close>
        by (meson b card_mono less_imp_le mult_left_mono of_nat_le_iff that(1) that(2))
      also have \<open>\<dots> = sum (\<lambda>_. b) Y\<close>
        by (simp add: mult.commute)
      also have \<open>\<dots> \<le> sum f Y\<close>
        using geqb by (meson subset_eq sum_mono that(3))
      finally show ?thesis
        by -
    qed
    ultimately show \<open>\<forall>\<^sub>F x in finite_subsets_at_top S. y < sum f x\<close>
      unfolding eventually_finite_subsets_at_top 
      by auto
  qed
  then show ?thesis
    unfolding infsum_def 
    apply (simp add: infsum_converges_ennreal)
    by (simp add: tendsto_Lim)
qed


end
