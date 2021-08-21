theory Infinite_Sum_Misc
  imports 
    "HOL-Library.Extended_Nonnegative_Real"
    "HOL-Analysis.Elementary_Topology"
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

lemma isCont_ennreal[simp]: \<open>isCont ennreal x\<close>
  apply (rule continuous_at_sequentiallyI)
  by simp

lemma tendsto_iff_uniformity:
  fixes l :: \<open>'b :: uniform_space\<close>
  shows \<open>(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>E. eventually E uniformity \<longrightarrow> (\<forall>\<^sub>F x in F. E (f x, l)))\<close>
proof (intro iffI allI impI)
  fix E :: \<open>('b \<times> 'b) \<Rightarrow> bool\<close>
  assume \<open>(f \<longlongrightarrow> l) F\<close> and \<open>eventually E uniformity\<close>
  from \<open>eventually E uniformity\<close>
  have \<open>eventually (\<lambda>(x, y). E (y, x)) uniformity\<close>
    by (simp add: uniformity_sym)
  then have \<open>\<forall>\<^sub>F (y, x) in uniformity. y = l \<longrightarrow> E (x, y)\<close>
    using eventually_mono by fastforce
  with \<open>(f \<longlongrightarrow> l) F\<close> have \<open>eventually (\<lambda>x. E (x ,l)) (filtermap f F)\<close>
    by (simp add: filterlim_def le_filter_def eventually_nhds_uniformity)
  then show \<open>\<forall>\<^sub>F x in F. E (f x, l)\<close>
    by (simp add: eventually_filtermap)
next
  assume assm: \<open>\<forall>E. eventually E uniformity \<longrightarrow> (\<forall>\<^sub>F x in F. E (f x, l))\<close>
  have \<open>eventually P (filtermap f F)\<close> if \<open>\<forall>\<^sub>F (x, y) in uniformity. x = l \<longrightarrow> P y\<close> for P
  proof -
    from that have \<open>\<forall>\<^sub>F (y, x) in uniformity. x = l \<longrightarrow> P y\<close> 
      using uniformity_sym[where E=\<open>\<lambda>(x,y). x=l \<longrightarrow> P y\<close>] by auto
    with assm have \<open>\<forall>\<^sub>F x in F. P (f x)\<close>
      by auto
    then show ?thesis
      by (auto simp: eventually_filtermap)
  qed
  then show \<open>(f \<longlongrightarrow> l) F\<close>
    by (simp add: filterlim_def le_filter_def eventually_nhds_uniformity)
qed

text \<open>The following should be the definition of \<^const>\<open>uniformity\<close> in an instantiation of \<open>prod :: (uniformity,uniformity) uniformity\<close>.
  However, we cannot define this instantiation because it would conflict with the existing 
  instantiation \<open>prod :: (metric_space, metric_space) uniformity_dist\<close> in \<^theory>\<open>HOL-Analysis.Product_Vector\<close>.
  Ideally, the latter instantiation would be replaced by \<open>prod :: (uniformity,uniformity) uniformity\<close>
  with the definition below.
  The existing definition (@{thm uniformity_prod_def} could then be derived as a corollary.
  (See \<open>uniformity_prod_compatible\<close> below.)
  Then the definition of \<open>uniformly_continuous2\<close> below would be unnecessary because it would be
  equivalent to \<open>uniformly_continuous_on UNIV\<close>.\<close>
definition \<open>uniformity_prod = (filtermap (\<lambda>((x1,x2),(y1,y2)). ((x1,y1),(x2,y2))) (uniformity \<times>\<^sub>F uniformity))\<close>

definition uniformly_continuous2 :: "(('a::uniform_space*'a2::uniform_space) \<Rightarrow> 'b::uniform_space) \<Rightarrow> bool"
  where "uniformly_continuous2 f \<longleftrightarrow> (LIM (x, y) uniformity_prod. (f x, f y) :> uniformity)"

lemma uniformity_prod_metric: \<open>uniformity_prod = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})\<close>
proof (subst filter_eq_iff, intro allI iffI)
  fix P :: \<open>('a \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> bool\<close>

  have 1: \<open>\<exists>e\<in>{0<..}.
              {(x,y). dist x y < e} \<subseteq> {(x,y). dist x y < a} \<and>
              {(x,y). dist x y < e} \<subseteq> {(x,y). dist x y < b}\<close> if \<open>a>0\<close> \<open>b>0\<close> for a b
    apply (rule bexI[of _ \<open>min a b\<close>])
    using that by auto
  have 2: \<open>mono (\<lambda>P. eventually (\<lambda>x. P (Q x)) F)\<close> for F :: \<open>'z filter\<close> and Q :: \<open>'z \<Rightarrow> 'y\<close>
    unfolding mono_def using eventually_mono le_funD by fastforce
  have \<open>\<forall>\<^sub>F ((x1::'a,y1),(x2::'b,y2)) in uniformity \<times>\<^sub>F uniformity. dist x1 y1 < e/2 \<and> dist x2 y2 < e/2\<close> if \<open>e>0\<close> for e
    by (auto intro!: eventually_prodI exI[of _ \<open>e/2\<close>] simp: case_prod_unfold eventually_uniformity_metric that)
  then have 3: \<open>\<forall>\<^sub>F ((x1::'a,y1),(x2::'b,y2)) in uniformity \<times>\<^sub>F uniformity. dist (x1,x2) (y1,y2) < e\<close> if \<open>e>0\<close> for e
    apply (rule eventually_rev_mp)
    by (auto intro!: that eventuallyI simp: case_prod_unfold dist_Pair_Pair sqrt_sum_squares_half_less)
  show \<open>eventually P (INF e\<in>{0<..}. principal {(x, y). dist x y < e}) \<Longrightarrow> 
        eventually P uniformity_prod\<close>
    apply (erule on_filter_baseE)
    using 1 3 by (auto simp: uniformity_prod_def case_prod_unfold eventually_filtermap 2)
next
  fix P :: \<open>('a \<times> 'b) \<times> ('a \<times> 'b) \<Rightarrow> bool\<close>
  assume \<open>eventually P uniformity_prod\<close>
  then obtain P1 P2 where \<open>eventually P1 uniformity\<close> \<open>eventually P2 uniformity\<close>
      and P1P2P: \<open>P1 (x1, y1) \<Longrightarrow> P2 (x2, y2) \<Longrightarrow> P ((x1, x2), (y1, y2))\<close> for x1 y1 x2 y2
    by (auto simp: eventually_filtermap case_prod_beta eventually_prod_filter uniformity_prod_def)
  from \<open>eventually P1 uniformity\<close> obtain e1 where \<open>e1>0\<close> and e1P1: \<open>dist x y < e1 \<Longrightarrow> P1 (x,y)\<close> for x y
    using eventually_uniformity_metric by blast
  from \<open>eventually P2 uniformity\<close> obtain e2 where \<open>e2>0\<close> and e2P2: \<open>dist x y < e2 \<Longrightarrow> P2 (x,y)\<close> for x y
    using eventually_uniformity_metric by blast
  define e where \<open>e = min e1 e2\<close>
  have \<open>e > 0\<close>
    using \<open>0 < e1\<close> \<open>0 < e2\<close> e_def by auto
  have \<open>dist (x1,x2) (y1,y2) < e \<Longrightarrow> dist x1 y1 < e1\<close> for x1 y1 :: 'a and x2 y2 :: 'b
    unfolding dist_prod_def e_def apply auto
    by (smt (verit, best) real_sqrt_sum_squares_ge1)
  moreover have \<open>dist (x1,x2) (y1,y2) < e \<Longrightarrow> dist x2 y2 < e2\<close> for x1 y1 :: 'a and x2 y2 :: 'b
    unfolding dist_prod_def e_def apply auto
    by (smt (verit, best) real_sqrt_sum_squares_ge1)
  ultimately have *: \<open>dist (x1,x2) (y1,y2) < e \<Longrightarrow> P ((x1, x2), (y1, y2))\<close> for x1 y1 x2 y2
    using e1P1 e2P2 P1P2P by auto

  show \<open>eventually P (INF e\<in>{0<..}. principal {(x, y). dist x y < e})\<close>
    apply (rule eventually_INF1[where i=e])
    using \<open>e > 0\<close> * by (auto simp: eventually_principal)
qed

lemma uniformly_continuous2_metricI:
  fixes f :: \<open>('a::metric_space \<times> 'b::metric_space) \<Rightarrow> 'c::metric_space\<close>
  assumes \<open>\<forall>e>0. \<exists>d>0. \<forall>(x::'a) y (x'::'b) y'. dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (f (x, x')) (f (y, y')) < e\<close>
  shows \<open>uniformly_continuous2 f\<close>
proof -
  have \<open>\<forall>\<^sub>F ((x,y),(x',y')) in uniformity \<times>\<^sub>F uniformity. dist (f (x,x')) (f (y,y')) < e\<close> if \<open>e > 0\<close> for e
  proof -
    obtain d where \<open>d > 0\<close> and d: \<open>dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (f (x,x')) (f (y,y')) < e\<close> for x y x' y'
      using assms(1) \<open>0 < e\<close> by blast
    have \<open>\<forall>\<^sub>F ((x,y),(x',y')) in uniformity \<times>\<^sub>F uniformity. dist x y < d \<and> dist x' y' < d\<close>
      unfolding case_prod_unfold apply (rule eventually_prodI)
      using eventually_uniformity_metric \<open>d > 0\<close> by force+
    then show ?thesis
      apply (rule eventually_mono)
      using d by auto
  qed
  then have \<open>eventually (\<lambda>((x,y),(x',y')). E (f (x,x'), f (y,y'))) (uniformity \<times>\<^sub>F uniformity)\<close> if \<open>eventually E uniformity\<close> for E
    apply (rule_tac on_filter_base_uniformity_distE[OF \<open>eventually E uniformity\<close>])
    by (auto simp: eventually_mono mono_def le_fun_def case_prod_unfold)
  then show ?thesis
    by (auto simp: uniformly_continuous2_def filterlim_def le_filter_def eventually_filtermap
        case_prod_unfold uniformity_prod_def)
qed

lemma uniformly_continuous2_plus_real_normed_vector[simp]:
  shows \<open>uniformly_continuous2 (\<lambda>(x::'a::real_normed_vector,y). x+y)\<close>
proof (rule uniformly_continuous2_metricI, intro allI impI, simp)
  fix e :: real assume \<open>0 < e\<close>
  show \<open>\<exists>d>0. \<forall>x y :: 'a. dist x y < d \<longrightarrow> (\<forall>x' y'. dist x' y' < d \<longrightarrow> dist (x + x') (y + y') < e)\<close>
    apply (rule exI[of _ \<open>e/2\<close>])
    using \<open>0 < e\<close> apply auto
    by (smt (verit, ccfv_SIG) dist_add_cancel dist_add_cancel2 dist_commute dist_triangle_lt)
qed

end
