theory Infsetsum_Infsum
  imports Infsetsum Infinite_Sum
begin

lemma abs_summable_infsum_exists:
  fixes f :: "'a\<Rightarrow>'b::{second_countable_topology,banach}" and A :: "'a set"
  assumes "f abs_summable_on A"
  shows "infsum_exists f A"
proof-
  define F where "F = filtermap (sum f) (finite_subsets_at_top A)"
  have F_not_bot: "F \<noteq> bot"
    unfolding F_def filtermap_bot_iff by simp

  have "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>x y. P x \<and> P y
         \<longrightarrow> dist (sum f x) (sum f y) < e)"
    if "0 < e"
    for e :: real
  proof-
    have is_SUP: "ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x)))"
    proof (rule infsetsum_nonneg_is_SUPREMUM_ereal)
      show "(\<lambda>x. norm (f x)) abs_summable_on A"
        by (simp add: assms)

      show "0 \<le> norm (f x)"
        if "x \<in> A"
        for x :: 'a
        using that
        by simp 
    qed 
    have "\<exists>F0\<in>{F. finite F \<and> F \<subseteq> A}.
       (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal e
       < ereal (\<Sum>x\<in>F0. norm (f x))"
      unfolding is_SUP Bex_def[symmetric]
      by (smt less_SUP_iff[symmetric] \<open>0 < e\<close> ereal_diff_le_self ereal_less_eq(5) ereal_minus(1) 
          is_SUP less_eq_ereal_def)
    then obtain F0 where "F0\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (\<Sum>x\<in>F0. norm (f x)) > ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) - ereal e"
      by (simp add: atomize_elim is_SUP) 
    hence [simp]: "finite F0" and [simp]: "F0 \<subseteq> A" 
      and sum_diff: "sum (\<lambda>x. norm (f x)) F0 > infsetsum (\<lambda>x. norm (f x)) A - e"
      by auto
    define P where "P F \<longleftrightarrow> finite F \<and> F \<supseteq> F0 \<and> F \<subseteq> A" for F
    have "dist (sum f F1) (sum f F2) < e" if "P F1" and "P F2" for F1 F2
    proof -
      from that(1) have "finite F1" and "F1 \<supseteq> F0" and "F1 \<subseteq> A" unfolding P_def by auto
      from that(2) have "finite F2" and "F2 \<supseteq> F0" and "F2 \<subseteq> A" unfolding P_def by auto
      have "dist (sum f F1) (sum f F2) = norm (sum f (F1-F2) - sum f (F2-F1))"
        unfolding dist_norm
        by (smt \<open>finite F1\<close> \<open>finite F2\<close> add_diff_cancel_left' add_diff_cancel_right' algebra_simps sum.Int_Diff sum.union_diff2 sum.union_inter) 
      also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) (F1-F2) + sum (\<lambda>x. norm (f x)) (F2-F1)"
        by (smt norm_triangle_ineq4 sum_norm_le)
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) (F1-F2) + infsetsum (\<lambda>x. norm (f x)) (F2-F1)"
        by (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) ((F1-F2)\<union>(F2-F1))"
      proof (rule infsetsum_Un_disjoint [symmetric])
        show "(\<lambda>x. norm (f x)) abs_summable_on F1 - F2"
          by (simp add: \<open>finite F1\<close>)          
        show "(\<lambda>x. norm (f x)) abs_summable_on F2 - F1"
          by (simp add: \<open>finite F2\<close>)          
        show "(F1 - F2) \<inter> (F2 - F1) = {}"
          by (simp add: Diff_Int_distrib2)          
      qed
      also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F0)"
      proof (rule infsetsum_mono_neutral_left)
        show "(\<lambda>x. norm (f x)) abs_summable_on F1 - F2 \<union> (F2 - F1)"
          by (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)          
        show "(\<lambda>x. norm (f x)) abs_summable_on A - F0"
          using abs_summable_on_subset assms by fastforce          
        show "norm (f x) \<le> norm (f x)"
          if "x \<in> F1 - F2 \<union> (F2 - F1)"
          for x :: 'a
          using that
          by simp 
        show "F1 - F2 \<union> (F2 - F1) \<subseteq> A - F0"
          by (simp add: Diff_mono \<open>F0 \<subseteq> F1\<close> \<open>F0 \<subseteq> F2\<close> \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close>)          
        show "0 \<le> norm (f x)"
          if "x \<in> A - F0 - (F1 - F2 \<union> (F2 - F1))"
          for x :: 'a
          by simp 
      qed
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) A - infsetsum (\<lambda>x. norm (f x)) F0"
        by (simp add: assms infsetsum_Diff)
      also have "\<dots> < e"
        using local.sum_diff by auto
      finally show "dist (sum f F1) (sum f F2) < e" by assumption
    qed
    moreover have "eventually P (finite_subsets_at_top A)"
      unfolding P_def eventually_finite_subsets_at_top
      using \<open>F0 \<subseteq> A\<close> \<open>finite F0\<close> by blast      
    ultimately show "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>F1 F2. P F1 \<and> P F2 \<longrightarrow> dist (sum f F1) (sum f F2) < e)"
      by auto
  qed
  hence cauchy: "cauchy_filter F"
    unfolding F_def cauchy_filter_metric_filtermap by auto
  from complete_UNIV have "F\<le>principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> (\<exists>x. F \<le> nhds x)"
    unfolding complete_uniform
    by auto
  have "(F \<le> principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> \<exists>x. F \<le> nhds x) \<Longrightarrow>
    \<exists>x. F \<le> nhds x"
    using cauchy F_not_bot by simp
  then obtain x where Fx: "F \<le> nhds x"
    using \<open>\<lbrakk>F \<le> principal UNIV; F \<noteq> bot; cauchy_filter F\<rbrakk> \<Longrightarrow> \<exists>x. F \<le> nhds x\<close> by blast
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding F_def
    by (simp add: filterlim_def)
  thus ?thesis
    unfolding infsum_exists_def by auto
qed

text \<open>The converse of @{thm abs_summable_infsum_exists} does not hold:
  Consider a separable infinite-dimensional Hilbert space of square-summable sequences.
  Let \<^term>\<open>e\<^sub>i\<close> denote the sequence with 1 in the \<^term>\<open>i\<close>th position, 0 elsewhere.
  Let \<^term>\<open>f (i::nat) = 1/i * e\<^sub>i\<close>. We have \<^term>\<open>\<not> f abs_summable_on UNIV\<close> because \<open>norm (f i) = 1/i\<close>
  and thus the sum over \<open>norm (f i)\<close> diverges. On the other hand, we have \<^term>\<open>infsum_exists f UNIV\<close>;
  the limit is the sequence with \<^term>\<open>1/i\<close> in the \<^term>\<open>i\<close>th position.

  (We have not formalized this separating example here because to the best of our knowledge,
  this Hilbert space has not been formalized in Isabelle/HOL yet.)
\<close>

lemma infsetsum_infsum:
  assumes "f abs_summable_on A"
  shows "infsetsum f A = infsum f A"
proof -
  have conv_sum_norm[simp]: "infsum_exists (\<lambda>x. norm (f x)) A"
  proof (rule abs_summable_infsum_exists)
    show "(\<lambda>x. norm (f x)) abs_summable_on A"
      using assms by simp
  qed    
  have "norm (infsetsum f A - infsum f A) \<le> \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = \<epsilon>/2"
    with that have [simp]: "\<delta> > 0" by simp
    obtain F1 where F1A: "F1 \<subseteq> A" and finF1: "finite F1" and leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F1) \<le> \<delta>"
    proof -
      have sum_SUP: "ereal (infsetsum (\<lambda>x. norm (f x)) A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum (\<lambda>x. norm (f x)) F))"
        (is "_ = ?SUP")
      proof (rule infsetsum_nonneg_is_SUPREMUM_ereal)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          by (simp add: assms)          
        show "0 \<le> norm (f x)"
          if "x \<in> A"
          for x :: 'a
          using that
          by simp 
      qed

      have "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal \<delta>
    < (SUP i\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>i. norm (f x)))"
        using \<open>\<delta>>0\<close>
        by (metis diff_strict_left_mono diff_zero ereal_less_eq(3) ereal_minus(1) not_le sum_SUP)
      then obtain F where "F\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (sum (\<lambda>x. norm (f x)) F) > ?SUP - ereal (\<delta>)"
        by (meson less_SUP_iff)
        
      hence "sum (\<lambda>x. norm (f x)) F > infsetsum (\<lambda>x. norm (f x)) A -  (\<delta>)"
        unfolding sum_SUP[symmetric] by auto
      hence "\<delta> > infsetsum (\<lambda>x. norm (f x)) (A-F)"
      proof (subst infsetsum_Diff)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that
          by (simp add: assms) 
        show "F \<subseteq> A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by blast 
        show "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - (\<Sum>\<^sub>ax\<in>F. norm (f x)) < \<delta>"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by auto 
      qed
      thus ?thesis using that 
        apply atomize_elim
        using \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> less_imp_le by blast
    qed
    have "\<exists>F2\<subseteq>A.
       finite F2 \<and>
       dist (\<Sum>x\<in>F2. norm (f x)) (infsum (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      using infsum_approx_sum[where f="(\<lambda>x. norm (f x))" and A=A and \<epsilon>=\<delta>]
        abs_summable_infsum_exists assms by auto
    then obtain F2 where F2A: "F2 \<subseteq> A" and finF2: "finite F2"
      and dist: "dist (sum (\<lambda>x. norm (f x)) F2) (infsum (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      by blast     
    have  leq_eps': "infsum (\<lambda>x. norm (f x)) (A-F2) \<le> \<delta>"
    proof (subst infsum_Diff)
      show "infsum_exists (\<lambda>x. norm (f x)) A"
        by simp        
      show "infsum_exists (\<lambda>x. norm (f x)) F2"
        by (simp add: finF2)        
      show "F2 \<subseteq> A"
        by (simp add: F2A)        
      show "infsum (\<lambda>x. norm (f x)) A - infsum (\<lambda>x. norm (f x)) F2 \<le> \<delta>"
        using dist finF2
        by (auto simp: dist_norm)
    qed 
    define F where "F = F1 \<union> F2"
    have FA: "F \<subseteq> A" and finF: "finite F" 
      unfolding F_def using F1A F2A finF1 finF2 by auto

    have "(\<Sum>\<^sub>ax\<in>A - (F1 \<union> F2). norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>A - F1. norm (f x))"
    proof (rule infsetsum_mono_neutral_left)
      show "(\<lambda>x. norm (f x)) abs_summable_on A - (F1 \<union> F2)"
        using abs_summable_on_subset assms by fastforce        
      show "(\<lambda>x. norm (f x)) abs_summable_on A - F1"
        using abs_summable_on_subset assms by fastforce        
      show "norm (f x) \<le> norm (f x)"
        if "x \<in> A - (F1 \<union> F2)"
        for x :: 'a
        using that
        by auto 
      show "A - (F1 \<union> F2) \<subseteq> A - F1"
        by (simp add: Diff_mono)        
      show "0 \<le> norm (f x)"
        if "x \<in> A - F1 - (A - (F1 \<union> F2))"
        for x :: 'a
        using that
        by auto 
    qed
    hence leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def
      using leq_eps by linarith
    have "infsum (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))
    \<le> infsum (\<lambda>x. norm (f x)) (A - F2)"
    proof (rule infsum_mono_set)
      show "0 \<le> norm (f x)"
        if "x \<in> A - F2 - (A - (F1 \<union> F2))"
        for x :: 'a
        using that
        by simp 
      show "A - (F1 \<union> F2) \<subseteq> A - F2"
        by (simp add: Diff_mono)        
      show "infsum_exists (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))"
        using F_def conv_sum_norm finF infsum_exists_cofin_subset by blast        
      show "infsum_exists (\<lambda>x. norm (f x)) (A - F2)"
        by (simp add: finF2 infsum_exists_cofin_subset)        
    qed
    hence leq_eps': "infsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def 
      by (rule order.trans[OF _ leq_eps'])
    have "norm (infsetsum f A - infsetsum f F) = norm (infsetsum f (A-F))"
    proof (subst infsetsum_Diff [symmetric])
      show "f abs_summable_on A"
        by (simp add: assms)          
      show "F \<subseteq> A"
        by (simp add: FA)          
      show "norm (infsetsum f (A - F)) = norm (infsetsum f (A - F))"
        by simp          
    qed
    also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F)"
      using norm_infsetsum_bound by blast
    also have "\<dots> \<le> \<delta>"
      using leq_eps by simp
    finally have diff1: "norm (infsetsum f A - infsetsum f F) \<le> \<delta>"
      by assumption
    have "norm (infsum f A - infsum f F) = norm (infsum f (A-F))"
    proof (subst infsum_Diff [symmetric])
      show "infsum_exists f A"
        by (simp add: abs_summable_infsum_exists assms)        
      show "infsum_exists f F"
        by (simp add: finF)        
      show "F \<subseteq> A"
        by (simp add: FA)        
      show "norm (infsum f (A - F)) = norm (infsum f (A - F))"
        by simp        
    qed
    also have "\<dots> \<le> infsum (\<lambda>x. norm (f x)) (A-F)"
      by (simp add: finF infsum_exists_cofin_subset norm_infsum_bound)
    also have "\<dots> \<le> \<delta>"
      using leq_eps' by simp
    finally have diff2: "norm (infsum f A - infsum f F) \<le> \<delta>"
      by assumption

    have x1: "infsetsum f F = infsum f F"
      using finF by simp
    have "norm (infsetsum f A - infsum f A) \<le> norm (infsetsum f A - infsetsum f F) + norm (infsum f A - infsum f F)"
      apply (rule_tac norm_diff_triangle_le)
       apply auto
      by (simp_all add: x1 norm_minus_commute)
    also have "\<dots> \<le> \<epsilon>"
      using diff1 diff2 \<delta>_def by linarith
    finally show ?thesis
      by assumption
  qed
  hence "norm (infsetsum f A - infsum f A) = 0"
    by (meson antisym_conv1 dense_ge norm_not_less_zero)
  thus ?thesis
    by auto
qed

end
