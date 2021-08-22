theory Infsetsum_Infsum
  imports Infsetsum Infinite_Sum
begin

text \<open>The following theorem relates \<^const>\<open>abs_summable_on\<close> with \<^const>\<open>infsum_exists\<close>.
  Note that while this theorem expresses an equivalence, the notion on the lhs is more general
  nonetheless because it applies to a wider range of types. (The rhs requires second countable
  Banach spaces while the lhs is well-defined on arbitrary real vector spaces.)\<close>

lemma norm_infsum_exists_iff_abs_summable_on: \<open>infsum_exists (\<lambda>x. norm (f x)) A \<longleftrightarrow> f abs_summable_on A\<close>
proof
  define n where \<open>n x = norm (f x)\<close> for x
  assume \<open>infsum_exists n A\<close>
  then have \<open>sum n F \<le> infsum n A\<close> if \<open>finite F\<close> and \<open>F\<subseteq>A\<close> for F
    using that by (auto simp flip: infsum_finite simp: n_def[abs_def] intro!: infsum_mono_neutral)
    
  then show \<open>f abs_summable_on A\<close>
    by (auto intro!: abs_summable_finiteI simp: n_def)
next
  define n where \<open>n x = norm (f x)\<close> for x
  assume \<open>f abs_summable_on A\<close>
  then have \<open>n abs_summable_on A\<close>
    by (simp add: \<open>f abs_summable_on A\<close> n_def)
  then have \<open>sum n F \<le> infsetsum n A\<close> if \<open>finite F\<close> and \<open>F\<subseteq>A\<close> for F
    using that by (auto simp flip: infsetsum_finite simp: n_def[abs_def] intro!: infsetsum_mono_neutral)
  then show \<open>infsum_exists n A\<close>
    apply (rule_tac pos_infsum_exists)
    by (auto simp add: n_def bdd_above_def)
qed

lemma abs_summable_infsum_exists:
  fixes f :: "'a\<Rightarrow>'b::{second_countable_topology,banach}" and A :: "'a set"
  assumes "f abs_summable_on A"
  shows "infsum_exists f A"
  apply (rule infsum_exists_norm_infsum_exists)
  by (simp add: assms norm_infsum_exists_iff_abs_summable_on)

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
      using infsum_finite_approximation[where f="(\<lambda>x. norm (f x))" and A=A and \<epsilon>=\<delta>]
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
      apply (rule infsum_mono_neutral)
      using finF by (auto simp add: finF2 infsum_exists_cofin_subset F_def)
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
