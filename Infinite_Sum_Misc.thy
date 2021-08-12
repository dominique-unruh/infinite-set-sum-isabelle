theory Infinite_Sum_Misc
  imports HOL.Real_Vector_Spaces HOL.Limits
begin

lemma cauchy_filter_metricI:
  fixes F :: "'a::metric_space filter"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
  shows "cauchy_filter F"
proof (unfold cauchy_filter_def le_filter_def, auto)
  fix P :: "'a \<times> 'a \<Rightarrow> bool"
  assume "eventually P uniformity"
  then obtain e where e: "e > 0" and P: "dist x y < e \<Longrightarrow> P (x, y)" for x y
    unfolding eventually_uniformity_metric by auto

  obtain P' where evP': "eventually P' F" and P'_dist: "P' x \<and> P' y \<Longrightarrow> dist x y < e" for x y
    apply atomize_elim using assms e by auto
  
  from evP' P'_dist P
  show "eventually P (F \<times>\<^sub>F F)"
    unfolding eventually_uniformity_metric eventually_prod_filter eventually_filtermap by metis
qed

lemma cauchy_filter_metric_filtermapI:
  fixes F :: "'a filter" and f :: "'a\<Rightarrow>'b::metric_space"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)"
  shows "cauchy_filter (filtermap f F)"
proof (rule cauchy_filter_metricI)
  fix e :: real assume e: "e > 0"
  with assms obtain P where evP: "eventually P F" and dist: "P x \<and> P y \<Longrightarrow> dist (f x) (f y) < e" for x y
    by atomize_elim auto
  define P' where "P' y = (\<exists>x. P x \<and> y = f x)" for y
  have "eventually P' (filtermap f F)"
    unfolding eventually_filtermap P'_def 
    using evP
    by (smt eventually_mono) 
  moreover have "P' x \<and> P' y \<longrightarrow> dist x y < e" for x y
    unfolding P'_def using dist by metis
  ultimately show "\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
    by auto
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
