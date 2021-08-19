theory Infinite_Sum_Misc
  imports HOL.Real_Vector_Spaces HOL.Limits
begin


lemma on_filter_baseE:
  assumes ev_INF: \<open>eventually P (INF e\<in>E. principal {x. R e x})\<close>
  assumes [simp]: \<open>E \<noteq> {}\<close>
  assumes \<open>\<And>a b. a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> \<exists>x\<in>E. Collect (R x) \<subseteq> Collect (R a) \<and> Collect (R x) \<subseteq> Collect (R b)\<close>
  assumes Q_mono: \<open>mono Q\<close>
  assumes rewritten: \<open>\<And>e. e \<in> E \<Longrightarrow> Q (R e)\<close>
  shows \<open>Q P\<close>
proof -
  obtain e where \<open>e \<in> E\<close> and \<open>eventually P (principal {x. R e x})\<close>
    using assms by (auto simp: eventually_INF_base)
  then have \<open>R e \<le> P\<close>
    unfolding eventually_principal
    by auto
  then have \<open>Q (R e) \<Longrightarrow> Q P\<close>
    using Q_mono
    by (metis le_boolE monoE)
  with rewritten \<open>e \<in> E\<close> show \<open>Q P\<close>
    by auto
qed

lemma on_filter_base_uniformity_distE:
  fixes P :: \<open>('a\<times>'a::{uniform_space,metric_space}) \<Rightarrow> bool\<close>
  assumes uni: \<open>eventually P uniformity\<close>
  assumes Q_mono: \<open>mono Q\<close>
  assumes rewritten: \<open>\<And>e. e > 0 \<Longrightarrow> Q (\<lambda>(x,y). dist x y < e)\<close>
  shows \<open>Q P\<close>
  using uni
  apply (subst (asm) uniformity_dist)
  apply (erule on_filter_baseE)
     apply (auto intro!: rewritten simp: Q_mono)
  subgoal for a b by (auto intro!: bexI[of _ \<open>min a b\<close>])
  by -


lemma cauchy_filter_metric:
  fixes F :: "'a::metric_space filter"
  shows "cauchy_filter F \<longleftrightarrow> (\<forall>e. e>0 \<longrightarrow> (\<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)))"
proof (unfold cauchy_filter_def le_filter_def, auto)
  assume assm: \<open>\<forall>e>0. \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
  then show \<open>eventually P uniformity \<Longrightarrow> eventually P (F \<times>\<^sub>F F)\<close> for P
    apply (erule_tac on_filter_base_uniformity_distE)
    apply (auto simp: mono_def case_prod_beta eventually_prod_same)
    apply (metis predicate1D) by metis
next
  fix e :: real
  assume \<open>e > 0\<close>
  assume asm: \<open>\<forall>P. eventually P uniformity \<longrightarrow> eventually P (F \<times>\<^sub>F F)\<close>

  define P where \<open>P \<equiv> \<lambda>(x,y :: 'a). dist x y < e\<close>
  with asm \<open>e > 0\<close> have \<open>eventually P (F \<times>\<^sub>F F)\<close>
    by (metis case_prod_conv eventually_uniformity_metric)
  then
  show \<open>\<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
    by (auto simp add: eventually_prod_same P_def)
qed

lemma cauchy_filter_metric_filtermap:
  shows "cauchy_filter (filtermap f F) \<longleftrightarrow> (\<forall>e. e>0 \<longrightarrow> (\<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)))"
proof (subst cauchy_filter_metric, intro iffI allI impI)
  assume \<open>\<forall>e>0. \<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
  then show \<open>e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)\<close> for e
    unfolding eventually_filtermap by blast
next
  assume asm: \<open>\<forall>e>0. \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)\<close>
  fix e::real assume \<open>e > 0\<close>
  then obtain P where \<open>eventually P F\<close> and PPe: \<open>P x \<and> P y \<longrightarrow> dist (f x) (f y) < e\<close> for x y
    using asm by blast

  show \<open>\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
    apply (rule exI[of _ \<open>\<lambda>x. \<exists>y. P y \<and> x = f y\<close>])
    using PPe \<open>eventually P F\<close> apply (auto simp: eventually_filtermap)
    by (smt (verit, ccfv_SIG) eventually_elim2)
qed

lemma tendsto_add_const_iff:
  \<comment> \<open>This is a generalization of \<open>Limits.tendsto_add_const_iff\<close>, 
      the only difference is that the sort here is more general.\<close>
  "((\<lambda>x. c + f x :: 'a::topological_group_add) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto


lemma finite_subsets_at_top_minus: 
  assumes "A\<subseteq>B"
  shows "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
proof (rule filter_leI)
  fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
  then obtain X where "finite X" and "X \<subseteq> B" 
    and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by auto

  hence "finite (X-A)" and "X-A \<subseteq> B - A"
    by auto
  moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
    using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
    by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
  ultimately show "eventually P (finite_subsets_at_top (B - A))"
    unfolding eventually_finite_subsets_at_top by meson
qed


lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
proof (rule filter_leI)
  show "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
    if "eventually P (finite_subsets_at_top A)"
    for P :: "'a set \<Rightarrow> bool"
    using that unfolding eventually_filtermap
    unfolding eventually_finite_subsets_at_top
    by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
qed


lemma tendsto_principal_singleton:
  shows "(f \<longlongrightarrow> f x) (principal {x})"
  unfolding tendsto_def eventually_principal by simp

end
