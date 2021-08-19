theory Infinite_Sum
  imports
    Infinite_Sum_Misc
    "HOL-Analysis.Elementary_Topology"
    "HOL-Library.Extended_Nonnegative_Real"
    Jordan_Normal_Form.Conjugate
    \<comment> \<open>\<^theory>\<open>Jordan_Normal_Form.Conjugate\<close> contains the instantiation \<open>complex :: ord\<close>.
               If we define our own instantiation, it would be impossible to load both
               \<^session>\<open>Jordan_Normal_Form\<close> and this theory.\<close>
begin

subsection\<open>Definition and syntax\<close>

definition infsum_exists :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "infsum_exists f A = (\<exists>x. (sum f \<longlongrightarrow> x) (finite_subsets_at_top A))"

definition infsum :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infsum f A = (if infsum_exists f A then Lim (finite_subsets_at_top A) (sum f) else 0)"

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


lemma 
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows infsum_exists_neutral_cong: "infsum_exists f S \<longleftrightarrow> infsum_exists g T" (is ?thesis_ex)
    and infsum_neutral_cong: \<open>infsum f S = infsum g T\<close> (is ?thesis_eq)
proof -
  have \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))
      = eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close> for P
  proof 
    assume \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> S\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (sum f F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> T\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> T\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (sum g F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> T\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (sum f ((F\<inter>S) \<union> (F0\<inter>S)))\<close>
        apply (rule F0_P)
        using \<open>F0 \<subseteq> S\<close>  \<open>finite F0\<close> that by auto
      also have \<open>sum f ((F\<inter>S) \<union> (F0\<inter>S)) = sum g F\<close>
        apply (rule sum.mono_neutral_cong)
        using that \<open>finite F0\<close> F0'_def assms by auto
      finally show ?thesis
        by -
    qed
    with \<open>F0' \<subseteq> T\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  next
    assume \<open>eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> T\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> T \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (sum g F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> S\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> S\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (sum f F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> S\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (sum g ((F\<inter>T) \<union> (F0\<inter>T)))\<close>
        apply (rule F0_P)
        using \<open>F0 \<subseteq> T\<close>  \<open>finite F0\<close> that by auto
      also have \<open>sum g ((F\<inter>T) \<union> (F0\<inter>T)) = sum f F\<close>
        apply (rule sum.mono_neutral_cong)
        using that \<open>finite F0\<close> F0'_def assms by auto
      finally show ?thesis
        by -
    qed
    with \<open>F0' \<subseteq> S\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  qed

  then have tendsto_x: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top S) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top T)" for x
    by (simp add: le_filter_def filterlim_def)

  then show ?thesis_ex
    by (simp add: infsum_exists_def)
  from tendsto_x show ?thesis_eq
    by (metis finite_subsets_at_top_neq_bot infsum_def infsum_exists_def tendsto_Lim)
qed


lemma infsum_exists_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum_exists f A = infsum_exists g A"
  by (metis (mono_tags, lifting) DiffE IntD1 infsum_exists_neutral_cong assms)

lemma infsum_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum f A = infsum g A"
  by (metis Diff_cancel assms empty_iff inf.idem infsum_neutral_cong)

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


lemma infsum_exists_cofin_subset:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsum_exists f A" and [simp]: "finite F"
  shows "infsum_exists f (A-F)"
proof-
  from assms(1) obtain x where lim_f: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding infsum_exists_def by auto
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
  thus "infsum_exists f (A - F)"
    unfolding infsum_exists_def by auto
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,t2_space}"
  assumes "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0"
  shows infsum_subset_zero: "infsum f A = infsum f B"
    and infsum_exists_subset_zero: "infsum_exists f A = infsum_exists f B"
proof -
  have convB: "infsum_exists f B" and eq: "infsum f A = infsum f B"
    if convA: "infsum_exists f A" and f0: "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0" for A B
  proof -
    define D where "D = (A-B)"
    define D' where "D' = B-A"

    from convA obtain x where limA: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using infsum_exists_def by blast
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
    thus "infsum_exists f B"
      unfolding infsum_exists_def by auto
    have "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top B) (sum f)"
      if "infsum_exists f B"
      using that    using limA limB
      using finite_subsets_at_top_neq_bot tendsto_Lim by blast
    thus "infsum f A = infsum f B"
      unfolding infsum_def 
      using convA
      by (simp add: \<open>infsum_exists f B\<close>)
  qed
  with assms show "infsum_exists f A = infsum_exists f B"
    by (metis Un_commute)
  thus "infsum f A = infsum f B"
    using assms convB eq
    by (metis infsum_def)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsum_exists f B" and "infsum_exists f A" and AB: "A \<subseteq> B"
  shows infsum_Diff: "infsum f (B - A) = infsum f B - infsum f A"
    and infsum_exists_Diff: "infsum_exists f (B-A)"
proof -
  define limA limB where "limA = infsum f A" and "limB = infsum f B"
  from assms(1) have limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    unfolding infsum_exists_def infsum_def limB_def
    by (auto simp: tendsto_Lim)
  from assms(2) have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)"
    unfolding infsum_exists_def infsum_def limA_def
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
  thus "infsum_exists f (B-A)"
    unfolding infsum_exists_def by auto
  with limBA show "infsum f (B - A) = limB - limA"
    unfolding infsum_def by (simp add: tendsto_Lim) 
qed

lemma infsum_mono_set:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes fx0: "\<And>x. x\<in>B-A \<Longrightarrow> f x \<ge> 0"
    and "A \<subseteq> B"
    and "infsum_exists f A" (* See infsum_exists_set_mono for why this assumption is needed. *)
    and "infsum_exists f B"
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
  have convA': "infsum_exists f' B"
  proof (rule infsum_exists_subset_zero [THEN iffD1 , where A1 = A])
    show "f' x = 0"
      if "x \<in> A - B \<union> (B - A)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsum_exists f' A"
      by (simp add: assms(3) f'_def infsum_exists_cong)      
  qed
  from assms have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)" 
    and limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    by (auto simp: limA_def limB_def infsum_exists_def infsum_def tendsto_Lim)
  have limA': "(sum f' \<longlongrightarrow> limA) (finite_subsets_at_top B)"
    using finite_subsets_at_top_neq_bot tendsto_Lim convA'
    unfolding limA_def' infsum_def  infsum_exists_def
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

lemma infsum_exists_finite[simp]:
  assumes "finite F"
  shows "infsum_exists f F"
  unfolding infsum_exists_def finite_subsets_at_top_finite[OF assms]
  using tendsto_principal_singleton by fastforce 

lemma infsum_finite[simp]:
  assumes "finite F"
  shows "infsum f F = sum f F"
  using assms by (auto intro: tendsto_Lim simp: finite_subsets_at_top_finite infsum_def principal_eq_bot_iff tendsto_principal_singleton)

lemma infsum_approx_sum:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "infsum_exists f A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsum f A) \<le> \<epsilon>"
proof -
  have "infsum_exists f A \<Longrightarrow>
    0 < \<epsilon> \<Longrightarrow> (sum f \<longlongrightarrow> Lim (finite_subsets_at_top A) (sum f)) (finite_subsets_at_top A)"
    unfolding infsum_exists_def
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
  assumes a1: "infsum_exists (\<lambda>x. norm (f x)) A"
  shows "norm (infsum f A) \<le> (infsum (\<lambda>x. norm (f x)) A)"
proof (cases "infsum_exists f A")
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
        show "infsum_exists (\<lambda>x. norm (f x)) F"
          using \<open>finite F\<close> by auto         
        show "infsum_exists (\<lambda>x. norm (f x)) A"
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
    using a1 unfolding infsum_exists_def by blast
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
      by (metis (no_types, lifting) False eventually_mono filterlim_iff infsum_exists_def)
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
  assumes \<open>infsum_exists f S\<close>
  shows \<open>((\<lambda>F. sum f F) \<longlongrightarrow> infsum f S) (finite_subsets_at_top S)\<close>
  by (metis assms finite_subsets_at_top_neq_bot infsum_exists_def infsum_def tendsto_Lim)

lemma infsum_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infsum (\<lambda>_. c) F = of_nat (card F) * c\<close>
  apply (subst infsum_finite[OF assms])
  by simp

lemma  
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows infsum_0: \<open>infsum f M = 0\<close>
    and infsum_ex_0: \<open>infsum_exists f M\<close>
proof -
  have \<open>(sum f \<longlongrightarrow> 0) (finite_subsets_at_top M)\<close>
    apply (subst tendsto_cong[where g=\<open>\<lambda>_. 0\<close>])
     apply (rule eventually_finite_subsets_at_top_weakI)
    using assms by (auto simp add: subset_iff)
  then show \<open>infsum f M = 0\<close> and \<open>infsum_exists f M\<close>
    unfolding infsum_def infsum_exists_def 
    by (auto simp add: tendsto_Lim)
qed

lemma  
  shows infsum_0_simp[simp]: \<open>infsum (\<lambda>_. 0) M = 0\<close>
    and infsum_ex_0_simp[simp]: \<open>infsum_exists (\<lambda>_. 0) M\<close>
  by (simp_all add: infsum_0 infsum_ex_0)

lemma
  fixes f g :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes \<open>infsum_exists f A\<close>
  assumes \<open>infsum_exists g A\<close>
  shows infsum_add: \<open>infsum (\<lambda>x. f x + g x) A = infsum f A + infsum g A\<close>
    and infsum_exists_add: \<open>infsum_exists (\<lambda>x. f x + g x) A\<close>
proof -
  note lim_f = infsum_tendsto[OF assms(1)]
    and lim_g = infsum_tendsto[OF assms(2)]
  then have lim: \<open>(sum (\<lambda>x. f x + g x) \<longlongrightarrow> infsum f A + infsum g A) (finite_subsets_at_top A)\<close>
    unfolding sum.distrib
    by (rule tendsto_add)
  then show conv: \<open>infsum_exists (\<lambda>x. f x + g x) A\<close>
    unfolding infsum_exists_def by auto
  show \<open>infsum (\<lambda>x. f x + g x) A = infsum f A + infsum g A\<close>
    unfolding infsum_def 
    using lim_f lim_g lim
    by (auto simp: assms conv tendsto_Lim)
qed

lemma 
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes "infsum_exists f A"
  assumes "infsum_exists f B"
  assumes disj: "A \<inter> B = {}"
  shows infsum_Un_disjoint: \<open>infsum f (A \<union> B) = infsum f A + infsum f B\<close>
    and infsum_exists_Un_disjoint: \<open>infsum_exists f (A \<union> B)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 0)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 0)\<close> for x
  have conv_fA: \<open>infsum_exists fA (A \<union> B)\<close>
    unfolding fA_def
    apply (subst infsum_exists_subset_zero, auto)
    by (simp add: assms(1) infsum_exists_cong)
  have conv_fB: \<open>infsum_exists fB (A \<union> B)\<close>
    unfolding fB_def
    apply (subst infsum_exists_subset_zero, auto)
    by (smt (verit, ccfv_SIG) assms(2) assms(3) disjoint_iff infsum_exists_cong)
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
  have \<open>infsum_exists (\<lambda>x. fA x + fB x) (A \<union> B)\<close>
    by (rule infsum_exists_add)
  then show \<open>infsum_exists f (A \<union> B)\<close>
    unfolding fAB by -
qed


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


(* Counterexample 1:

  Consider the real vector space V of sequences with finite support, and with the l2-norm (sum of squares).
  Let e_i denote the sequence with a 1 at position i.
  Let f : \<int>\<Rightarrow>V be defined as f n = e_{abs n} / n (with f 0 = 0)
  We have that \<open>infsum f \<int> = 0\<close> (it even converges absolutely). 
  But \<open>infsum f \<nat>\<close> does not exist (it would converge against a sequence with infinite support).

  Counterexample 2:

  Let f be a positive rational valued function such that "sum f B" is sqrt(2) and "sum f A" is 1 (over the reals, with A\<le>B).
  Then "sum f B" does not exist over the rationals. But "sum f A" exists.

  Not sure if the condition "plus_cont" is required. *)

lemma infsum_exists_set_mono:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,t2_space,uniform_space}\<close>
  assumes \<open>complete (UNIV :: 'b set)\<close>
  assumes plus_cont: \<open>\<And>E::('b\<times>'b) \<Rightarrow> bool. eventually E uniformity \<Longrightarrow> \<exists>D. eventually D uniformity \<and> (\<forall>x y c. D (x+c, y+c) \<longrightarrow> E (x, y))\<close>
  assumes \<open>infsum_exists f A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>infsum_exists f B\<close>
proof -
  from \<open>infsum_exists f A\<close>
  obtain S where \<open>(sum f \<longlongrightarrow> S) (finite_subsets_at_top A)\<close> (is \<open>(sum f \<longlongrightarrow> S) ?filter_A\<close>)
    using infsum_exists_def by blast
  then have cauchy_fA: \<open>cauchy_filter (filtermap (sum f) (finite_subsets_at_top A))\<close> (is \<open>cauchy_filter ?filter_fA\<close>)
    by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)

  let ?filter_fB = \<open>filtermap (sum f) (finite_subsets_at_top B)\<close>

  have \<open>cauchy_filter (filtermap (sum f) (finite_subsets_at_top B))\<close>
  proof (unfold cauchy_filter_def, rule filter_leI)
    fix E :: \<open>('b\<times>'b) \<Rightarrow> bool\<close> assume \<open>eventually E uniformity\<close>
    then obtain E' where \<open>eventually E' uniformity\<close> and E'E'E: \<open>E' (x, y) \<longrightarrow> E' (y, z) \<longrightarrow> E (x, z)\<close> for x y z
      using uniformity_trans by blast
    obtain D where \<open>eventually D uniformity\<close> and DE: \<open>D (x + c, y + c) \<Longrightarrow> E' (x, y)\<close> for x y c
      apply atomize_elim using \<open>eventually E' uniformity\<close> by (rule plus_cont)
    with cauchy_fA have \<open>eventually D (?filter_fA \<times>\<^sub>F ?filter_fA)\<close>
      unfolding cauchy_filter_def le_filter_def by simp
    then obtain P1 P2 where ev_P1: \<open>eventually (\<lambda>F. P1 (sum f F)) ?filter_A\<close> and ev_P2: \<open>eventually (\<lambda>F. P2 (sum f F)) ?filter_A\<close>
      and P1P2E: \<open>P1 x \<Longrightarrow> P2 y \<Longrightarrow> D (x, y)\<close> for x y
      unfolding eventually_prod_filter eventually_filtermap
      by auto
    from ev_P1 obtain F1 where \<open>finite F1\<close> and \<open>F1 \<subseteq> A\<close> and \<open>\<forall>F. F\<supseteq>F1 \<and> finite F \<and> F\<subseteq>A \<longrightarrow> P1 (sum f F)\<close>
      by (metis eventually_finite_subsets_at_top)
    from ev_P2 obtain F2 where \<open>finite F2\<close> and \<open>F2 \<subseteq> A\<close> and \<open>\<forall>F. F\<supseteq>F2 \<and> finite F \<and> F\<subseteq>A \<longrightarrow> P2 (sum f F)\<close>
      by (metis eventually_finite_subsets_at_top)
    define F0 F0A F0B where \<open>F0 \<equiv> F1 \<union> F2\<close> and \<open>F0A \<equiv> F0 - B\<close> and \<open>F0B \<equiv> F0 \<inter> B\<close>
    have [simp]: \<open>finite F0\<close>  \<open>F0 \<subseteq> A\<close>
       apply (simp add: F0_def \<open>finite F1\<close> \<open>finite F2\<close>)
      by (simp add: F0_def \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close>)
    have [simp]: \<open>finite F0A\<close>
      by (simp add: F0A_def)
    have \<open>\<forall>F1 F2. F1\<supseteq>F0 \<and> F2\<supseteq>F0 \<and> finite F1 \<and> finite F2 \<and> F1\<subseteq>A \<and> F2\<subseteq>A \<longrightarrow> D (sum f F1, sum f F2)\<close>
      by (simp add: F0_def P1P2E \<open>\<forall>F. F1 \<subseteq> F \<and> finite F \<and> F \<subseteq> A \<longrightarrow> P1 (sum f F)\<close> \<open>\<forall>F. F2 \<subseteq> F \<and> finite F \<and> F \<subseteq> A \<longrightarrow> P2 (sum f F)\<close>)
    then have \<open>\<forall>F1 F2. F1\<supseteq>F0B \<and> F2\<supseteq>F0B \<and> finite F1 \<and> finite F2 \<and> F1\<subseteq>B \<and> F2\<subseteq>B \<longrightarrow> 
              D (sum f (F1 \<union> F0A), sum f (F2 \<union> F0A))\<close>
      by (smt (verit) Diff_Diff_Int Diff_subset_conv F0A_def F0B_def \<open>F0 \<subseteq> A\<close> \<open>finite F0A\<close> assms(4) finite_UnI sup.absorb_iff1 sup.mono sup_commute)
    then have \<open>\<forall>F1 F2. F1\<supseteq>F0B \<and> F2\<supseteq>F0B \<and> finite F1 \<and> finite F2 \<and> F1\<subseteq>B \<and> F2\<subseteq>B \<longrightarrow> 
              D (sum f F1 + sum f F0A, sum f F2 + sum f F0A)\<close>
      by (metis Diff_disjoint F0A_def \<open>finite F0A\<close> inf.absorb_iff1 inf_assoc inf_bot_right sum.union_disjoint)
    then have *: \<open>\<forall>F1 F2. F1\<supseteq>F0B \<and> F2\<supseteq>F0B \<and> finite F1 \<and> finite F2 \<and> F1\<subseteq>B \<and> F2\<subseteq>B \<longrightarrow> 
              E' (sum f F1, sum f F2)\<close>
      by (auto intro!: DE[where c=\<open>sum f F0A\<close>])
    show \<open>eventually E (?filter_fB \<times>\<^sub>F ?filter_fB)\<close>
      apply (subst eventually_prod_filter)
      apply (rule exI[of _ \<open>\<lambda>x. E' (x, sum f F0B)\<close>])
      apply (rule exI[of _ \<open>\<lambda>x. E' (sum f F0B, x)\<close>])
      apply (auto simp: eventually_filtermap)
      using * apply (metis (no_types, lifting) F0B_def Int_lower2 \<open>finite F0\<close> eventually_finite_subsets_at_top finite_Int order_refl)
      using * apply (metis (no_types, lifting) F0B_def Int_lower2 \<open>finite F0\<close> eventually_finite_subsets_at_top finite_Int order_refl)
      using E'E'E by auto
  qed

  then obtain x where \<open>filtermap (sum f) (finite_subsets_at_top B) \<le> nhds x\<close>
    apply atomize_elim
    apply (rule complete_uniform[where S=UNIV, THEN iffD1, rule_format, simplified])
    using assms by (auto simp add: filtermap_bot_iff)

  then have \<open>(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)\<close>
    by (auto simp: filterlim_def)
  then show ?thesis
    by (auto simp: infsum_exists_def)
qed

lemma infsum_exists_set_mono_metric:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,complete_space}\<close>
  assumes \<open>\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. (\<forall>x y c :: 'b. dist (x+c) (y+c) < d \<longrightarrow> dist x y < e)\<close>
  assumes \<open>infsum_exists f A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>infsum_exists f B\<close>
proof -
  have \<open>complete (UNIV::'b set)\<close>
    by (metis Cauchy_convergent UNIV_I complete_def convergent_def)
  have cont: \<open>eventually E uniformity \<Longrightarrow> \<exists>D. eventually D uniformity \<and> (\<forall>x y c. D (x + c, y + c) \<longrightarrow> E (x, y))\<close> for E :: \<open>('b\<times>'b) \<Rightarrow> bool\<close>
  proof (erule on_filter_base_uniformity_distE, unfold case_prod_conv)
    show \<open>mono (\<lambda>a. \<exists>D. eventually D uniformity \<and> (\<forall>x y c. D (x + c, y + c) \<longrightarrow> a (x, y)))\<close>
      by (smt (z3) le_bool_def le_fun_def mono_def)
    fix e :: real assume \<open>0 < e\<close>
    obtain d where \<open>d > 0\<close> and de: \<open>dist (x+c) (y+c) < d \<longrightarrow> dist x y < e\<close> for x y c :: 'b
      using \<open>0 < e\<close> assms(1) by blast
    show \<open>\<exists>D. eventually D uniformity \<and> (\<forall>x y c::'b. D (x + c, y + c) \<longrightarrow> dist x y < e)\<close>
      apply (rule exI[of _ \<open>\<lambda>(x,y). dist x y < d\<close>])
      using de \<open>d > 0\<close> by (auto simp: eventually_uniformity_metric)
  qed
  show ?thesis
    using \<open>complete (UNIV::'b set)\<close>  cont \<open>infsum_exists f A\<close> \<open>B \<subseteq> A\<close> 
    by (rule infsum_exists_set_mono[where A=A])
qed

lemma infsum_exists_set_mono_banach:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,banach}\<close>
  assumes \<open>infsum_exists f A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>infsum_exists f B\<close>
  apply (rule infsum_exists_set_mono_metric)
  using assms by auto

lemma infsum_exists_union_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> infsum_exists f (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>infsum_exists f (\<Union>a\<in>A. B a)\<close>
  using finite conv disj apply induction by (auto intro!: infsum_exists_Un_disjoint)

lemma sum_infsum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_monoid_add, t2_space, comm_monoid_add}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> infsum_exists f (B a)\<close>
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
    using insert.prems insert.hyps by (auto simp: infsum_exists_union_disjoint)
  also have \<open>\<dots> = infsum f (\<Union>a\<in>insert x F. B a)\<close>
    by auto
  finally show ?case
    by -
qed

theorem infsum_mono:
  fixes f g :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}" (* Does it also hold in order_topology? *)
  assumes "infsum_exists f A"
    and "infsum_exists g A"
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

lemma 
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>infsum_exists g S\<close>
  shows infsum_additive0_ex: \<open>infsum_exists (f o g) S\<close> 
    and infsum_additive0: \<open>infsum (f o g) S = f (infsum g S)\<close>
proof -
  have \<open>(sum g \<longlongrightarrow> infsum g S) (finite_subsets_at_top S)\<close>
    by (simp add: assms(3) infsum_tendsto)
  then have \<open>((f o sum g) \<longlongrightarrow> f (infsum g S)) (finite_subsets_at_top S)\<close>
    using assms(2) isContD tendsto_compose_at by blast
  then have *: \<open>(sum (f o g) \<longlongrightarrow> f (infsum g S)) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_cong[THEN iffD1, rotated])
    using f_sum by fastforce
  show \<open>infsum_exists (f o g) S\<close> 
    and \<open>infsum (f o g) S = f (infsum g S)\<close>
    apply (meson * infsum_exists_def)
    by (metis * finite_subsets_at_top_neq_bot infsum_exists_def infsum_def tendsto_Lim)
qed

lemma 
  assumes \<open>additive f\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>infsum_exists g S\<close>
  shows infsum_additive_ex: \<open>infsum_exists (f o g) S\<close> 
    and infsum_additive: \<open>infsum (f o g) S = f (infsum g S)\<close>
   apply (rule infsum_additive0_ex; auto simp: assms additive.sum)
  by (rule infsum_additive0; auto simp: assms additive.sum)

subsection \<open>Infinite sum over specific monoids\<close>

lemma infsum_exists_ennreal[simp]: \<open>infsum_exists (f::_ \<Rightarrow> ennreal) S\<close>
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
    unfolding infsum_exists_def
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
    apply (simp add: infsum_exists_ennreal)
    by (simp add: tendsto_Lim)
qed


subsection \<open>UNSORTED\<close>


lemma infsum_exists_iff[simp]:
  "infsum_exists (\<lambda>i. cnj (f i)) A \<longleftrightarrow> infsum_exists f A"
proof auto
  assume assm: \<open>infsum_exists (\<lambda>x. cnj (f x)) A\<close>
  then have \<open>infsum_exists (\<lambda>x. cnj (cnj (f x))) A\<close>
    apply (rule_tac infsum_additive_ex[where f=cnj, unfolded o_def])
    by (auto intro!: additive.intro)
  then show \<open>infsum_exists f A\<close>
    by simp
next
  assume \<open>infsum_exists f A\<close>
  then show \<open>infsum_exists (\<lambda>x. cnj (f x)) A\<close>
    apply (rule_tac infsum_additive_ex[where f=cnj, unfolded o_def])
    by (auto intro!: additive.intro)
qed

lemma infsetsum_cnj[simp]: \<open>infsum (\<lambda>x. cnj (f x)) M = cnj (infsum f M)\<close>
proof (cases \<open>infsum_exists f M\<close>)
  case True
  then show ?thesis
    apply (rule_tac infsum_additive[where f=cnj, unfolded o_def])
    by (auto intro!: additive.intro)
next
  case False
  then have 1: \<open>infsum f M = 0\<close>
    by (simp add: infsum_def)
  from False have \<open>\<not> infsum_exists (\<lambda>x. cnj (f x)) M\<close>
    by simp
  then have 2: \<open>infsum (\<lambda>x. cnj (f x)) M = 0\<close>
    by (simp add: infsum_def)
  from 1 2 show ?thesis
    by simp
qed

lemma infsum_Re: 
  assumes "infsum_exists f M"
  shows "infsum (\<lambda>x. Re (f x)) M = Re (infsum f M)"
  apply (rule infsum_additive[where f=Re, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma infsum_exists_Re: 
  assumes "infsum_exists f M"
  shows "infsum_exists (\<lambda>x. Re (f x)) M"
  apply (rule infsum_additive_ex[where f=Re, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma infsum_Im: 
  assumes "infsum_exists f M"
  shows "infsum (\<lambda>x. Im (f x)) M = Im (infsum f M)"
  apply (rule infsum_additive[where f=Im, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma infsum_exists_Im: 
  assumes "infsum_exists f M"
  shows "infsum_exists (\<lambda>x. Im (f x)) M"
  apply (rule infsum_additive_ex[where f=Im, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma infsum_mono_complex:
  \<comment> \<open>For \<^typ>\<open>real\<close>, @{thm infsum_mono} can be used. But \<^typ>\<open>complex\<close> does not have the right typeclass.\<close>
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "infsum_exists f A" and g_sum: "infsum_exists g A"
  assumes leq: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsum f A \<le> infsum g A"
proof -
  from leq have \<open>Im (f x) = Im (g x)\<close> if \<open>x \<in> A\<close> for x
    using that by force
  then have \<open>infsum (Im o f) A = infsum (Im o g) A\<close>
    apply (rule_tac infsum_cong)
    by simp
  moreover have \<open>infsum (Im o f) A = Im (infsum f A)\<close>
    by (metis (mono_tags, lifting) comp_apply f_sum infsum_Im infsum_cong)
  moreover have \<open>infsum (Im o g) A = Im (infsum g A)\<close>
    by (metis (mono_tags, lifting) comp_apply g_sum infsum_Im infsum_cong)
  ultimately have Im: \<open>Im (infsum f A) = Im (infsum g A)\<close>
    by auto

  have conv_Re_f: \<open>infsum_exists (Re \<circ> f) A\<close>
    by (simp add: f_sum infsum_exists_Re infsum_exists_cong)
  have conv_Re_g: \<open>infsum_exists (Re \<circ> g) A\<close>
    by (simp add: g_sum infsum_exists_Re infsum_exists_cong)

  from leq have \<open>Re (f x) \<le> Re (g x)\<close> if \<open>x \<in> A\<close> for x
    using that by force
  then have \<open>infsum (Re o f) A \<le> infsum (Re o g) A\<close>
    apply (rule_tac infsum_mono)
    using conv_Re_f conv_Re_g by auto
  moreover have \<open>infsum (Re o f) A = Re (infsum f A)\<close>
    by (metis (mono_tags, lifting) comp_apply f_sum infsum_Re infsum_cong)
  moreover have \<open>infsum (Re o g) A = Re (infsum g A)\<close>
    by (metis (mono_tags, lifting) comp_apply g_sum infsum_Re infsum_cong)
  ultimately have Re: \<open>Re (infsum f A) \<le> Re (infsum g A)\<close>
    by auto

  from Im Re show \<open>infsum f A \<le> infsum g A\<close>
    by auto
qed

lemma infsetsum_subset_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "infsum_exists f B" and "A \<subseteq> B" and "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows "infsum f A \<le> infsum f B"
    \<comment> \<open>Existence of \<^term>\<open>infsum f A\<close> follows from @{thm infsum_exists_set_mono_banach}\<close>
proof -
  have *: \<open>infsum_exists f A\<close>
    using \<open>infsum_exists f B\<close> \<open>A \<subseteq> B\<close> by (rule infsum_exists_set_mono_banach)
  show ?thesis
    apply (rule infsum_mono_set)
    using assms * by auto
qed

lemma infsetsum_subset_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "infsum_exists f B" and "A \<subseteq> B" and pos: "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows "infsum f A \<le> infsum f B"
    \<comment> \<open>Existence of \<^term>\<open>infsum f A\<close> follows from @{thm infsum_exists_set_mono_banach}\<close>
proof -
  have \<open>infsum (\<lambda>x. Re (f x)) A \<le> infsum (\<lambda>x. Re (f x)) B\<close>
    apply (rule infsetsum_subset_real)
    using assms infsum_exists_Re by auto
  then have Re: \<open>Re (infsum f A) \<le> Re (infsum f B)\<close>
    by (metis assms(1) assms(2) infsum_Re infsum_exists_set_mono_banach)
  have \<open>infsum (\<lambda>x. Im (f x)) A = infsum (\<lambda>x. Im (f x)) B\<close>
    apply (rule infsum_neutral_cong)
    using pos assms by auto
  then have Im: \<open>Im (infsum f A) = Im (infsum f B)\<close>
    by (metis assms(1) assms(2) infsum_Im infsum_exists_set_mono_banach)
  from Re Im show ?thesis
    by auto
qed

lemma
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows pos_infsum_exists: \<open>infsum_exists f A\<close> (is ?ex)
    and pos_infsum: \<open>infsum f A = (SUP F\<in>{F. F\<subseteq>A \<and> finite F}. sum f F)\<close> (is ?sum)
proof -
  have *: \<open>(sum f \<longlongrightarrow> (SUP F\<in>{F. F\<subseteq>A \<and> finite F}. sum f F)) (finite_subsets_at_top A)\<close>
  proof (rule order_tendstoI)
    fix a assume \<open>a < (SUP F\<in>{F. F\<subseteq>A \<and> finite F}. sum f F)\<close>
    then obtain F where \<open>a < sum f F\<close> and \<open>finite F\<close> and \<open>F \<subseteq> A\<close>
      by (metis (mono_tags, lifting) Collect_empty_eq assms(2) empty_subsetI finite.emptyI less_cSUP_iff mem_Collect_eq)
    show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. a < sum f x\<close>
      unfolding eventually_finite_subsets_at_top
      apply (rule exI[of _ F])
      using \<open>a < sum f F\<close> and \<open>finite F\<close> and \<open>F \<subseteq> A\<close>
      apply auto
      by (smt (verit, best) Diff_iff assms(1) less_le_trans subset_iff sum_mono2)
  next
    fix a assume \<open>(SUP F\<in>{F. F\<subseteq>A \<and> finite F}. sum f F) < a\<close>
    then have \<open>sum f F < a\<close> if \<open>F\<subseteq>A\<close> and \<open>finite F\<close> for F
      using assms cSUP_lessD that(1) that(2) by fastforce
    then show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x < a\<close>
      by (rule eventually_finite_subsets_at_top_weakI)
  qed

  from * show ?ex
    by (auto simp add: infsum_exists_def)
  with * show ?sum
    by (simp add: infsum_def tendsto_Lim)
qed

lemma
  fixes f :: \<open>'a \<Rightarrow> 'b :: {complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows pos_infsum_exists_complete: \<open>infsum_exists f A\<close> (is ?ex)
    and pos_infsum_complete: \<open>infsum f A = (SUP F\<in>{F. F\<subseteq>A \<and> finite F}. sum f F)\<close> (is ?sum)
  using assms apply (rule pos_infsum_exists; simp)
  using assms by (rule pos_infsum; simp)

(* TODO move *)
lemma isCont_ennreal[simp]: \<open>isCont ennreal x\<close>
  apply (rule continuous_at_sequentiallyI)
  by simp

lemma infsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "infsum_exists f A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof -
  have \<open>ennreal (infsum f A) = infsum (ennreal o f) A\<close>
    apply (rule infsum_additive0[symmetric])
    apply (subst sum_ennreal[symmetric])
    using assms by auto
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))\<close>
    apply (subst pos_infsum_complete, simp)
    apply (rule SUP_cong, blast)
    apply (subst sum_ennreal[symmetric])
    using fnn by auto
  finally show ?thesis
    by -
qed

lemma infsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "infsum_exists f A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have \<open>ereal (infsum f A) = infsum (ereal o f) A\<close>
    apply (rule infsum_additive0[symmetric])
    using assms by auto
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))\<close>
    apply (subst pos_infsum_complete)
     apply (simp_all add: assms)[2]
    apply (rule SUP_cong, blast)
    using fnn by auto
  finally show ?thesis
    by -
qed

lemma infsetsum_nonneg_is_SUPREMUM:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "infsum_exists f A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsum f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
proof -
  have "ereal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
    using assms by (rule infsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
  proof (subst ereal_SUP)
    show "\<bar>SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a)\<bar> \<noteq> \<infinity>"
      using calculation by fastforce      
    show "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f F)) = (SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a))"
      by simp      
  qed
  finally show ?thesis by simp
qed


(* TODO: same for linorder *)
lemma infsetsum_geq0_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "infsum_exists f M"
    and "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0" (is "?lhs \<ge> _")
proof -
  note less_eq_complex_def[simp del]
  have \<open>infsum f M \<ge> infsum (\<lambda>_. 0) M\<close>
    apply (rule infsum_mono_complex)
    using assms by auto
  then show ?thesis
    by simp
qed

lemma infsetsum_cmod:
  assumes "infsum_exists f M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum (\<lambda>x. cmod (f x)) M = cmod (infsum f M)"
proof -
  have \<open>complex_of_real (infsum (\<lambda>x. cmod (f x)) M) = infsum (\<lambda>x. complex_of_real (cmod (f x))) M\<close>
    apply (rule infsum_additive[symmetric, unfolded o_def])
    apply auto
    apply (simp add: additive.intro)
    by (smt (verit, best) assms(1) cmod_eq_Re fnn infsum_exists_Re infsum_exists_cong less_eq_complex_def zero_complex.simps(1) zero_complex.simps(2))
  also have \<open>\<dots> = infsum f M\<close>
    apply (rule infsum_cong)
    using fnn
    using cmod_eq_Re complex_is_Real_iff by force
  finally show ?thesis
    by (metis abs_of_nonneg infsum_def le_less_trans norm_ge_zero norm_infsum_bound norm_of_real not_le order_refl)
qed

(* TODO move *)
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

(* TODO move *)
lemma uniformity_multi_trans:
  fixes E :: \<open>('a \<times> 'a::uniform_space) \<Rightarrow> bool\<close>
  assumes \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually (\<lambda>(x,y). D x y) uniformity\<close>
    and \<open>\<And>m. m \<le> n \<Longrightarrow> D ^^ m \<le> (\<lambda>x y. E (x, y))\<close>
proof (atomize_elim, induction n)
  case 0
  show ?case
    by (metis assms bot_nat_0.extremum_unique case_prod_eta refl_ge_eq relpowp.simps(1) uniformity_refl)
next
  define E' where \<open>E' x y = E (x,y)\<close> for x y
  case (Suc n)
  show ?case
  proof (cases \<open>n=0\<close>)
    case True
    then show ?thesis 
      using assms apply (auto intro!: exI[of _ \<open>\<lambda>x y. E (x, y)\<close>])
      by (metis (mono_tags, lifting) One_nat_def eq_OO eq_iff le_less_linear less_one relpowp.simps(1) relpowp.simps(2) uniformity_refl)
  next
    case False
    from Suc obtain D where \<open>eventually (case_prod D) uniformity\<close> and D_multitrans: \<open>\<forall>m\<le>n. (D ^^ m) \<le> E'\<close>
      by (auto simp: E'_def le_fun_def)
    obtain D' where D'_uni: \<open>eventually (case_prod D') uniformity\<close> and D'_trans: \<open>D' OO D' \<le> D\<close>
      using uniformity_trans[OF \<open>eventually (case_prod D) uniformity\<close>]
      apply atomize_elim apply (auto simp: le_fun_def OO_def)
      by (metis case_prod_eta)
    have \<open>D' \<le> D\<close>
      using D'_trans D'_uni uniformity_refl by fastforce
    then have pow_mono: \<open>(D' ^^ m) \<le> (D ^^ m)\<close> for m
      apply (induction m) by auto

    have \<open>D' ^^ Suc n = D' OO D' OO (D' ^^ (n-1))\<close>
      by (metis False diff_Suc_1 not0_implies_Suc relpowp.simps(2) relpowp_commute)
    also from D'_trans have \<open>\<dots> \<le> D OO (D' ^^ (n-1))\<close>
      by blast
    also have \<open>\<dots> \<le> D OO (D ^^ (n-1))\<close>
      using pow_mono by blast
    also have \<open>\<dots> = D ^^ n\<close>
      by (metis Suc_pred' neq0_conv relpowp.simps(2) relpowp_commute False)
    also have \<open>\<dots> \<le> E'\<close>
      using D_multitrans by blast
    finally have D'_Sn: \<open>D' ^^ Suc n \<le> E'\<close>
      by -

    from D_multitrans have D'_n: \<open>\<forall>m\<le>n. (D' ^^ m) \<le> E'\<close>
      by (meson order_trans pow_mono)

    from D'_Sn D'_n D'_uni
    show ?thesis
      apply (auto intro!: exI[of _ D'])
      by (metis D'_Sn E'_def le_Suc_eq predicate2D)
  qed
qed

(* TODO move *)
lemma uniformity_eventually_trans[trans]:
  fixes A B C :: \<open>'a \<Rightarrow> 'b :: uniform_space\<close>
  assumes \<open>\<forall>E. eventually E uniformity \<longrightarrow> eventually (\<lambda>x. E (A x, B x)) F\<^sub>1\<close>
  assumes \<open>\<forall>E. eventually E uniformity \<longrightarrow> eventually (\<lambda>x. E (B x, C x)) F\<^sub>2\<close>
  shows \<open>\<forall>E. eventually E uniformity \<longrightarrow> eventually (\<lambda>x. E (A x, C x)) (inf F\<^sub>1 F\<^sub>2)\<close>
proof (intro allI impI)
  fix E :: \<open>('b \<times> 'b) \<Rightarrow> bool\<close>
  assume \<open>eventually E uniformity\<close>
  then obtain D where \<open>eventually D uniformity\<close> and DDE: \<open>D (x, y) \<Longrightarrow> D (y, z) \<Longrightarrow> E (x, z)\<close> for x y z
    apply (rule uniformity_transE) by auto
  with assms have \<open>eventually (\<lambda>x. D (A x, B x)) F\<^sub>1\<close> and \<open>eventually (\<lambda>x. D (B x, C x)) F\<^sub>2\<close>
    by auto
  then show \<open>eventually (\<lambda>x. E (A x, C x)) (inf F\<^sub>1 F\<^sub>2)\<close>
    using DDE eventually_inf by blast
qed


(* TODO move *)
lemma indexed_list_sum:
  assumes \<open>distinct L\<close>
  shows \<open>(\<Sum>i<length L. f (L!i)) = (\<Sum>x\<in>set L. f x)\<close>
  using assms apply (induction L rule:rev_induct)
   apply auto
  by (metis (no_types, lifting) add.commute lessThan_iff nth_append sum.cong)

lemma sum_uniformity:
  (* TODO: replace by simpler equivalent condition (one-sided uniform continuity but D independent of choice of added constant *)
  assumes plus_cont: \<open>\<And>E::('b\<times>'b::{uniform_space,comm_monoid_add}) \<Rightarrow> bool. eventually E uniformity \<Longrightarrow> eventually (\<lambda>((x,y),(x',y')). E (x+x', y+y')) (uniformity \<times>\<^sub>F uniformity)\<close>
  assumes \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually D uniformity\<close> 
    and \<open>\<And>M::'a set. \<And>f f' :: 'a \<Rightarrow> 'b. card M \<le> n \<and> (\<forall>m\<in>M. D (f m, f' m)) \<Longrightarrow> E (sum f M, sum f' M)\<close>
proof (atomize_elim, insert \<open>eventually E uniformity\<close>, induction n arbitrary: E rule:nat_induct)
  case 0
  then show ?case
    by (metis card_eq_0_iff equals0D le_zero_eq sum.infinite sum.not_neutral_contains_not_neutral uniformity_refl)
next
  case (Suc n)
  
  from plus_cont[OF Suc.prems]
  obtain D1 D2 where \<open>eventually D1 uniformity\<close> and \<open>eventually D2 uniformity\<close> 
    and D1D2E: \<open>D1 (x, y) \<Longrightarrow> D2 (x', y') \<Longrightarrow> E (x + x', y + y')\<close> for x y x' y'
    apply atomize_elim unfolding eventually_prod_filter by auto

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


lemma plus_uniform_cont_metric:
  fixes E :: \<open>('a\<times>'a::{metric_space,plus}) \<Rightarrow> bool\<close>
  assumes \<open>\<forall>e>0. \<exists>d>0. \<forall>x y x' y' :: 'a. dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (x+x') (y+y') < e\<close>
  assumes \<open>eventually E uniformity\<close>
  shows \<open>eventually (\<lambda>((x,y),(x',y')). E (x+x', y+y')) (uniformity \<times>\<^sub>F uniformity)\<close>
proof -
  have \<open>\<forall>\<^sub>F ((x::'a,y),(x',y')) in uniformity \<times>\<^sub>F uniformity. dist (x+x') (y+y') < e\<close> if \<open>e > 0\<close> for e
  proof -
    obtain d where \<open>d > 0\<close> and d: \<open>dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (x+x') (y+y') < e\<close> for x y x' y' :: 'a
      using assms(1) \<open>0 < e\<close> by blast
    have \<open>\<forall>\<^sub>F ((x,y),(x',y')) in uniformity \<times>\<^sub>F uniformity. dist x y < d \<and> dist x' y' < d\<close>
      unfolding case_prod_unfold apply (rule eventually_prodI)
      using eventually_uniformity_metric \<open>d > 0\<close> by force+
    then show ?thesis
      apply (rule eventually_mono)
      using d by auto
  qed
  then show ?thesis
    apply (rule_tac on_filter_base_uniformity_distE[OF \<open>eventually E uniformity\<close>])
    by (auto simp: eventually_mono mono_def le_fun_def case_prod_unfold)
qed

lemma plus_uniform_cont_norm:
  fixes E :: \<open>('a\<times>'a::{real_normed_vector}) \<Rightarrow> bool\<close>
  assumes \<open>eventually E uniformity\<close>
  shows \<open>eventually (\<lambda>((x,y),(x',y')). E (x+x', y+y')) (uniformity \<times>\<^sub>F uniformity)\<close>
proof (rule plus_uniform_cont_metric; intro allI impI assms)
  fix e :: real assume \<open>0 < e\<close>
  show \<open>\<exists>d>0. \<forall>x y x' y' :: 'a. dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (x + x') (y + y') < e\<close>
    apply (rule exI[of _ \<open>e/2\<close>])
    using \<open>0 < e\<close> apply auto
    by (smt (verit, ccfv_SIG) dist_add_cancel dist_add_cancel2 dist_commute dist_triangle_lt)
qed

lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,uniform_space}\<close>
  assumes plus_cont: \<open>\<And>E::('c\<times>'c) \<Rightarrow> bool. eventually E uniformity \<Longrightarrow> eventually (\<lambda>((x,y),(x',y')). E (x+x', y+y')) (uniformity \<times>\<^sub>F uniformity)\<close>
  assumes summableAB: "infsum_exists f (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> infsum_exists (\<lambda>y. f (x, y)) (B x)\<close>
  shows infsetsum_Sigma: "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
    and infsetsum_Sigma_exists: \<open>infsum_exists (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A\<close>
proof -
  define S SB SAB where \<open>S = infsum f (Sigma A B)\<close> and \<open>SB x = infsum (\<lambda>y. f (x, y)) (B x)\<close> 
    and \<open>SAB = infsum SB A\<close> for x
  define F FB FA where \<open>F = finite_subsets_at_top (Sigma A B)\<close> and \<open>FB x = finite_subsets_at_top (B x)\<close>
    and \<open>FA = finite_subsets_at_top A\<close> for x

  from summableB
  have sum_SB: \<open>(sum (\<lambda>y. f (x, y)) \<longlongrightarrow> SB x) (FB x)\<close> if \<open>x \<in> A\<close> for x
    by (simp add: FB_def SB_def infsum_tendsto that)
  from summableAB
  have sum_S: \<open>(sum f \<longlongrightarrow> S) F\<close>
    by (simp add: F_def SB_def[abs_def] S_def infsum_tendsto)

  have finite_proj: \<open>finite {b| b. (a,b) \<in> H}\<close> if \<open>finite H\<close> for H :: \<open>('a\<times>'b) set\<close> and a
    apply (subst asm_rl[of \<open>{b| b. (a,b) \<in> H} = snd ` {ab. ab \<in> H \<and> fst ab = a}\<close>])
    by (auto simp: image_iff that)

  have \<open>(sum SB \<longlongrightarrow> S) FA\<close>
  proof (rule tendsto_iff_uniformity[THEN iffD2, rule_format])
    fix E :: \<open>('c \<times> 'c) \<Rightarrow> bool\<close>
    assume \<open>eventually E uniformity\<close>
    then obtain D where D_uni: \<open>eventually D uniformity\<close> and DDE': \<open>\<And>x y z. D (x, y) \<Longrightarrow> D (y, z) \<Longrightarrow> E (x, z)\<close>
      by (metis (no_types, lifting) \<open>eventually E uniformity\<close> uniformity_transE)
    from sum_S obtain G where \<open>finite G\<close> and \<open>G \<subseteq> Sigma A B\<close>
      and G_sum: \<open>G \<subseteq> H \<Longrightarrow> H \<subseteq> Sigma A B \<Longrightarrow> finite H \<Longrightarrow> D (sum f H, S)\<close> for H
      unfolding tendsto_iff_uniformity
      by (metis (mono_tags, lifting) D_uni F_def eventually_finite_subsets_at_top)
    have \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> by auto
    thm uniformity_prod_def
    define Ga where \<open>Ga a = {b. (a,b) \<in> G}\<close> for a
    have Ga_fin: \<open>finite (Ga a)\<close> and Ga_B: \<open>Ga a \<subseteq> B a\<close> for a
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> finite_proj by (auto simp: Ga_def finite_proj)

    have \<open>E (sum SB M, S)\<close> if \<open>M \<supseteq> fst ` G\<close> and \<open>finite M\<close> and \<open>M \<subseteq> A\<close> for M
    proof -
      define FMB where \<open>FMB = finite_subsets_at_top (Sigma M B)\<close>
      have \<open>eventually (\<lambda>H. D (\<Sum>a\<in>M. SB a, \<Sum>(a,b)\<in>H. f (a,b))) FMB\<close>
      proof -
        obtain D' where D'_uni: \<open>eventually D' uniformity\<close> 
          and \<open>card M' \<le> card M \<and> (\<forall>m\<in>M'. D' (g m, g' m)) \<Longrightarrow> D (sum g M', sum g' M')\<close>
            for M' :: \<open>'a set\<close> and g g'
          apply (rule sum_uniformity[OF plus_cont \<open>eventually D uniformity\<close>, where n=\<open>card M\<close>])
          by auto
        then have D'_sum_D: \<open>(\<forall>m\<in>M. D' (g m, g' m)) \<Longrightarrow> D (sum g M, sum g' M)\<close> for g g'
          by auto

        obtain Ha where \<open>Ha a \<supseteq> Ga a\<close> and Ha_fin: \<open>finite (Ha a)\<close> and Ha_B: \<open>Ha a \<subseteq> B a\<close>
          and D'_sum_Ha: \<open>Ha a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (SB a, sum (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
        proof -
          from sum_SB[unfolded tendsto_iff_uniformity, rule_format, OF _ D'_uni[THEN uniformity_sym]]
          obtain Ha0 where \<open>finite (Ha0 a)\<close> and \<open>Ha0 a \<subseteq> B a\<close>
            and \<open>Ha0 a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (SB a, sum (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
            unfolding FB_def eventually_finite_subsets_at_top apply auto by metis
          moreover define Ha where \<open>Ha a = Ha0 a \<union> Ga a\<close> for a
          ultimately show ?thesis
            using that[where Ha=Ha]
            using Ga_fin Ga_B by auto
        qed

        have \<open>D (\<Sum>a\<in>M. SB a, \<Sum>(a,b)\<in>H. f (a,b))\<close> if \<open>finite H\<close> and \<open>H \<subseteq> Sigma M B\<close> and \<open>H \<supseteq> Sigma M Ha\<close> for H
        proof -
          define Ha' where \<open>Ha' a = {b| b. (a,b) \<in> H}\<close> for a
          have [simp]: \<open>finite (Ha' a)\<close> and [simp]: \<open>Ha' a \<supseteq> Ha a\<close> and [simp]: \<open>Ha' a \<subseteq> B a\<close> if \<open>a \<in> M\<close> for a
            unfolding Ha'_def using \<open>finite H\<close> \<open>H \<subseteq> Sigma M B\<close> \<open>Sigma M Ha \<subseteq> H\<close> that finite_proj by auto
          have \<open>Sigma M Ha' = H\<close>
            using that by (auto simp: Ha'_def)
          then have *: \<open>(\<Sum>(a,b)\<in>H. f (a,b)) = (\<Sum>a\<in>M. \<Sum>b\<in>Ha' a. f (a,b))\<close>
            apply (subst sum.Sigma)
            using \<open>finite M\<close> by auto
          have \<open>D' (SB a, sum (\<lambda>b. f (a,b)) (Ha' a))\<close> if \<open>a \<in> M\<close> for a
            apply (rule D'_sum_Ha)
            using that \<open>M \<subseteq> A\<close> by auto
          then have \<open>D (\<Sum>a\<in>M. SB a, \<Sum>a\<in>M. sum (\<lambda>b. f (a,b)) (Ha' a))\<close>
            by (rule_tac D'_sum_D, auto)
          with * show ?thesis
            by auto
        qed
        moreover have \<open>Sigma M Ha \<subseteq> Sigma M B\<close>
          using Ha_B \<open>M \<subseteq> A\<close> by auto
        ultimately show ?thesis
          apply (simp add: FMB_def eventually_finite_subsets_at_top)
          by (metis Ha_fin finite_SigmaI subsetD that(2) that(3))
      qed
      moreover have \<open>eventually (\<lambda>H. D (\<Sum>(a,b)\<in>H. f (a,b), S)) FMB\<close>
        unfolding FMB_def eventually_finite_subsets_at_top
        apply (rule exI[of _ G])
        using \<open>G \<subseteq> Sigma A B\<close> \<open>finite G\<close> that G_sum apply auto
        by (smt (z3) Sigma_Un_distrib1 dual_order.trans subset_Un_eq)
      ultimately have \<open>\<forall>\<^sub>F x in FMB. E (sum SB M, S)\<close>
        by (smt (verit, best) DDE' eventually_elim2)
      then show \<open>E (sum SB M, S)\<close>
        apply (rule eventually_const[THEN iffD1, rotated])
        using FMB_def by force
    qed
    then show \<open>\<forall>\<^sub>F x in FA. E (sum SB x, S)\<close>
      using \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      by (auto intro!: exI[of _ \<open>fst ` G\<close>] simp add: FA_def eventually_finite_subsets_at_top)
  qed
  then show \<open>S = (\<Sum>\<^sub>\<infinity>a\<in>A. SB a)\<close>
    by (metis FA_def finite_subsets_at_top_neq_bot infsum_def infsum_exists_def tendsto_Lim)
  show \<open>infsum_exists SB A\<close>
    using FA_def \<open>(sum SB \<longlongrightarrow> S) FA\<close> infsum_exists_def by blast
qed

lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,metric_space}\<close>
  assumes \<open>\<forall>e>0. \<exists>d>0. \<forall>x y x' y' :: 'c. dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (x+x') (y+y') < e\<close>
  assumes "infsum_exists f (Sigma A B)"
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> infsum_exists (\<lambda>y. f (x, y)) (B x)\<close>
  shows infsetsum_Sigma_metric: "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
    and infsetsum_Sigma_metric_exists: "infsum_exists (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
  subgoal apply (rule infsetsum_Sigma) using assms by (auto simp add: plus_uniform_cont_metric)
  subgoal apply (rule infsetsum_Sigma_exists) using assms by (auto simp add: plus_uniform_cont_metric)
  by -

lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{real_normed_vector}\<close>
  assumes "infsum_exists f (Sigma A B)"
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> infsum_exists (\<lambda>y. f (x, y)) (B x)\<close>
  shows infsetsum_Sigma_normed: "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
    and infsetsum_Sigma_normed_exists: "infsum_exists (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
  subgoal apply (rule infsetsum_Sigma) using assms by (auto simp add: plus_uniform_cont_norm)
  subgoal apply (rule infsetsum_Sigma_exists) using assms by (auto simp add: plus_uniform_cont_norm)
  by -

lemma 
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,uniform_space}\<close>
  assumes plus_cont: \<open>\<And>E::('c\<times>'c) \<Rightarrow> bool. eventually E uniformity \<Longrightarrow> eventually (\<lambda>((x,y),(x',y')). E (x+x', y+y')) (uniformity \<times>\<^sub>F uniformity)\<close>
  assumes "infsum_exists (\<lambda>(x,y). f x y) (Sigma A B)"
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> infsum_exists (f x) (B x)\<close>
  shows infsetsum_Sigma': "infsum (\<lambda>x. infsum (f x) (B x)) A = infsum (\<lambda>(x,y). f x y) (Sigma A B)"
    and infsetsum_Sigma_exists': \<open>infsum_exists (\<lambda>x. infsum (f x) (B x)) A\<close>
  apply (subst infsetsum_Sigma) using assms apply auto
  by -

lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,metric_space}\<close>
  assumes \<open>\<forall>e>0. \<exists>d>0. \<forall>x y x' y' :: 'c. dist x y < d \<longrightarrow> dist x' y' < d \<longrightarrow> dist (x+x') (y+y') < e\<close>
  assumes "infsum_exists (\<lambda>(x,y). f x y) (Sigma A B)"
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> infsum_exists (f x) (B x)\<close>
  shows infsetsum_Sigma_metric': "infsum (\<lambda>x. infsum (f x) (B x)) A = infsum (\<lambda>(x,y). f x y) (Sigma A B)"
    and infsetsum_Sigma_metric_exists': \<open>infsum_exists (\<lambda>x. infsum (f x) (B x)) A\<close>
  subgoal apply (rule infsetsum_Sigma') using assms by (auto simp add: plus_uniform_cont_metric)
  subgoal apply (rule infsetsum_Sigma_exists') using assms by (auto simp add: plus_uniform_cont_metric)
  by -

lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{real_normed_vector}\<close>
  assumes "infsum_exists (\<lambda>(x,y). f x y) (Sigma A B)"
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> infsum_exists (f x) (B x)\<close>
  shows infsetsum_Sigma_norm': "infsum (\<lambda>x. infsum (f x) (B x)) A = infsum (\<lambda>(x,y). f x y) (Sigma A B)"
    and infsetsum_Sigma_norm_exists': \<open>infsum_exists (\<lambda>x. infsum (f x) (B x)) A\<close>
  subgoal apply (rule infsetsum_Sigma') using assms by (auto simp add: plus_uniform_cont_norm)
  apply (rule infsetsum_Sigma_exists') using assms by (auto simp add: plus_uniform_cont_norm)

(* TODO: remove _Times variants also in Infsetsum.thy *)

lemma
  assumes \<open>inj_on h A\<close>
  shows infsum_reindex: \<open>infsum g (h ` A) = infsum (g \<circ> h) A\<close> (is ?thesis1)
    and infsum_exists_reindex: \<open>infsum_exists g (h ` A) \<longleftrightarrow> infsum_exists (g \<circ> h) A\<close> (is ?thesis2)
proof -
  have \<open>(sum g \<longlongrightarrow> x) (finite_subsets_at_top (h ` A)) \<longleftrightarrow> ((\<lambda>F. sum g (h ` F)) \<longlongrightarrow> x) (finite_subsets_at_top A)\<close> for x
    apply (subst filtermap_image_finite_subsets_at_top[symmetric])
    using assms by (auto simp: filterlim_def filtermap_filtermap)
  also have \<open>\<dots> x \<longleftrightarrow> (sum (g \<circ> h) \<longlongrightarrow> x) (finite_subsets_at_top A)\<close> for x
    apply (rule tendsto_cong)
    apply (rule eventually_finite_subsets_at_top_weakI)
    apply (rule sum.reindex)
    using assms subset_inj_on by blast
  finally show ?thesis1 ?thesis2
    apply (auto simp: infsum_exists_def)
    by (metis finite_subsets_at_top_neq_bot infsum_def infsum_exists_def tendsto_Lim)
qed

lemma infsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,uniform_space}"
  assumes plus_cont: \<open>\<And>E::('c\<times>'c) \<Rightarrow> bool. eventually E uniformity \<Longrightarrow> eventually (\<lambda>((x,y),(x',y')). E (x+x', y+y')) (uniformity \<times>\<^sub>F uniformity)\<close>
  assumes \<open>infsum_exists (\<lambda>(x, y). f x y) (A \<times> B)\<close>
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> infsum_exists (f a) B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> infsum_exists (\<lambda>a. f a b) A\<close>
  shows "infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B"
proof -
  have [simp]: \<open>infsum_exists (\<lambda>(x, y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infsum_exists_reindex)
    using assms by (auto simp: o_def)
  have \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    apply (subst infsetsum_Sigma)
    using assms by auto
  also have \<open>\<dots> = infsum (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infsum_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
    apply (subst infsetsum_Sigma)
    using assms by auto
  finally show ?thesis
    by -
qed

(* TODO: variants of infsum_swap (_metric, _norm, _banach) *)

lemma abs_summable_partition:
  fixes T :: "'b set" and I :: "'a set"
  assumes "\<And>i. f abs_summable_on S i"
  and "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on I"
  and "T \<subseteq> (\<Union>i\<in>I. S i)"
  shows "f abs_summable_on T"

lemma abs_summable_product':
  fixes X :: "'a set" and Y :: "'b set"
  assumes "\<And>x. (\<lambda>y. f (x,y)) abs_summable_on Y"
    and "(\<lambda>x. \<Sum>\<^sub>ay\<in>Y. norm (f (x,y))) abs_summable_on X"
  shows "f abs_summable_on X\<times>Y"

lemma infsetsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A"
    and summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsetsum (f x) (B x))"

lemma infsetsum_0D:
  fixes f :: "'a \<Rightarrow> real"
  assumes "infsetsum f A = 0"
  and abs_sum: "f abs_summable_on A"
  and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  and "x \<in> A"
  shows "f x = 0"

lemma sum_leq_infsetsum:
  fixes f :: "_ \<Rightarrow> real"
  assumes "f abs_summable_on N"
  and "finite M"
  and "M \<subseteq> N"
  and "\<And>x. x\<in>N-M \<Longrightarrow> f x \<ge> 0"
  shows "sum f M \<le> infsetsum f N"

lemma infsetsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology, division_ring}"
  shows  "infsetsum (\<lambda>x. f x * c) A = infsetsum f A * c"

lemma abs_summable_on_zero_diff:
  assumes "f abs_summable_on A"
  and "\<And>x. x \<in> B - A \<Longrightarrow> f x = 0"
  shows "f abs_summable_on B"

lemma abs_summable_on_Sigma_iff:
  "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"

lemma
  fixes f :: "'a \<Rightarrow> 'c :: {banach, real_normed_field, second_countable_topology}"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  shows   abs_summable_on_product: "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    and   infsetsum_product: "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) =
                                infsetsum f A * infsetsum g B"

end

