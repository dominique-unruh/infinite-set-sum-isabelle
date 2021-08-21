theory Deleted
  imports HOL.Topological_Spaces
begin

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

lemma indexed_list_sum:
  assumes \<open>distinct L\<close>
  shows \<open>(\<Sum>i<length L. f (L!i)) = (\<Sum>x\<in>set L. f x)\<close>
  using assms apply (induction L rule:rev_induct)
   apply auto
  by (metis (no_types, lifting) add.commute lessThan_iff nth_append sum.cong)


end
