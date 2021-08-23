section \<open>Miscellanea\<close>

text \<open>This theory proves various (topology-related) facts that are not specific to infinite sums
  and that are not found in the Isabelle standard library.\<close>

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

lemma sum_uniformity:
  assumes plus_cont: \<open>uniformly_continuous2 (\<lambda>(x::'b::{uniform_space,comm_monoid_add},y). x+y)\<close>
  assumes \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually D uniformity\<close> 
    and \<open>\<And>M::'a set. \<And>f f' :: 'a \<Rightarrow> 'b. card M \<le> n \<and> (\<forall>m\<in>M. D (f m, f' m)) \<Longrightarrow> E (sum f M, sum f' M)\<close>
proof (atomize_elim, insert \<open>eventually E uniformity\<close>, induction n arbitrary: E rule:nat_induct)
  case 0
  then show ?case
    by (metis card_eq_0_iff equals0D le_zero_eq sum.infinite sum.not_neutral_contains_not_neutral uniformity_refl)
next
  case (Suc n)
  
  from plus_cont[unfolded uniformly_continuous2_def filterlim_def le_filter_def, rule_format, OF Suc.prems]
  obtain D1 D2 where \<open>eventually D1 uniformity\<close> and \<open>eventually D2 uniformity\<close> 
    and D1D2E: \<open>D1 (x, y) \<Longrightarrow> D2 (x', y') \<Longrightarrow> E (x + x', y + y')\<close> for x y x' y'
    apply atomize_elim
    by (auto simp: eventually_prod_filter case_prod_beta uniformity_prod_def eventually_filtermap)

  from Suc.IH[OF \<open>eventually D2 uniformity\<close>]
  obtain D3 where \<open>eventually D3 uniformity\<close> and D3: \<open>card M \<le> n \<Longrightarrow> (\<forall>m\<in>M. D3 (f m, f' m)) \<Longrightarrow> D2 (sum f M, sum f' M)\<close> 
    for M :: \<open>'a set\<close> and f f'
    by metis

  define D where \<open>D x \<equiv> D1 x \<and> D3 x\<close> for x
  have \<open>eventually D uniformity\<close>
    using D_def \<open>eventually D1 uniformity\<close> \<open>eventually D3 uniformity\<close> eventually_elim2 by blast

  have \<open>E (sum f M, sum f' M)\<close> 
    if \<open>card M \<le> Suc n\<close> and DM: \<open>\<forall>m\<in>M. D (f m, f' m)\<close>
    for M :: \<open>'a set\<close> and f f'
  proof (cases \<open>card M = 0\<close>)
    case True
    then show ?thesis
      by (metis Suc.prems card_eq_0_iff sum.empty sum.infinite uniformity_refl) 
  next
    case False
    with \<open>card M \<le> Suc n\<close> obtain N x where \<open>card N \<le> n\<close> and \<open>x \<notin> N\<close> and \<open>M = insert x N\<close>
      by (metis card_Suc_eq less_Suc_eq_0_disj less_Suc_eq_le)

    from DM have \<open>\<And>m. m\<in>N \<Longrightarrow> D (f m, f' m)\<close>
      using \<open>M = insert x N\<close> by blast
    with D3[OF \<open>card N \<le> n\<close>]
    have D2_N: \<open>D2 (sum f N, sum f' N)\<close>
      using D_def by blast

    from DM 
    have \<open>D (f x, f' x)\<close>
      using \<open>M = insert x N\<close> by blast
    then have \<open>D1 (f x, f' x)\<close>
      by (simp add: D_def)

    with D2_N
    have \<open>E (f x + sum f N, f' x + sum f' N)\<close>
      using D1D2E by presburger

    then show \<open>E (sum f M, sum f' M)\<close>
      by (metis False \<open>M = insert x N\<close> \<open>x \<notin> N\<close> card.infinite finite_insert sum.insert)
  qed
  with \<open>eventually D uniformity\<close>
  show ?case 
    by auto
qed

lemma ennreal_of_enat_plus[simp]: \<open>ennreal_of_enat (a+b) = ennreal_of_enat a + ennreal_of_enat b\<close>
  apply (induction a)
  apply auto
  by (smt (z3) add.commute add.right_neutral enat.exhaust enat.simps(4) enat.simps(5) ennreal_add_left_cancel ennreal_of_enat_def infinity_ennreal_def of_nat_add of_nat_eq_enat plus_enat_simps(2))

lemma sum_ennreal_of_enat[simp]: "(\<Sum>i\<in>I. ennreal_of_enat (f i)) = ennreal_of_enat (sum f I)"
  apply (induction I rule: infinite_finite_induct) 
  by (auto simp: sum_nonneg)

lemma isCont_ennreal_of_enat[simp]: \<open>isCont ennreal_of_enat x\<close>
proof (subst continuous_at_open, intro allI impI, cases \<open>x = \<infinity>\<close>)
  case True
  note True[simp]

  fix t assume \<open>open t \<and> ennreal_of_enat x \<in> t\<close>
  then have \<open>\<exists>y<\<infinity>. {y <.. \<infinity>} \<subseteq> t\<close>
    apply (rule_tac open_left[where y=0])
    by auto
  then obtain y where \<open>{y<..} \<subseteq> t\<close> and \<open>y \<noteq> \<infinity>\<close>
    apply atomize_elim
    apply (auto simp: greaterThanAtMost_def)
    by (metis atMost_iff inf.orderE subsetI top.not_eq_extremum top_greatest)

  from \<open>y \<noteq> \<infinity>\<close>
  obtain x' where x'y: \<open>ennreal_of_enat x' > y\<close> and \<open>x' \<noteq> \<infinity>\<close>
    by (metis enat.simps(3) ennreal_Ex_less_of_nat ennreal_of_enat_enat infinity_ennreal_def top.not_eq_extremum)
  define s where \<open>s = {x'<..}\<close>
  have \<open>open s\<close>
    by (simp add: s_def)
  moreover have \<open>x \<in> s\<close>
    by (simp add: \<open>x' \<noteq> \<infinity>\<close> s_def)
  moreover have \<open>ennreal_of_enat z \<in> t\<close> if \<open>z \<in> s\<close> for z
    by (metis x'y \<open>{y<..} \<subseteq> t\<close> ennreal_of_enat_le_iff greaterThan_iff le_less_trans less_imp_le not_less s_def subsetD that)
  ultimately show \<open>\<exists>s. open s \<and> x \<in> s \<and> (\<forall>z\<in>s. ennreal_of_enat z \<in> t)\<close>
    by auto
next
  case False
  fix t assume asm: \<open>open t \<and> ennreal_of_enat x \<in> t\<close>
  define s where \<open>s = {x}\<close>
  have \<open>open s\<close>
    using False open_enat_iff s_def by blast
  moreover have \<open>x \<in> s\<close>
    using s_def by auto
  moreover have \<open>ennreal_of_enat z \<in> t\<close> if \<open>z \<in> s\<close> for z
    using asm s_def that by blast
  ultimately show \<open>\<exists>s. open s \<and> x \<in> s \<and> (\<forall>z\<in>s. ennreal_of_enat z \<in> t)\<close>
    by auto
qed


end
