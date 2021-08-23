section \<open>Infinite sums as defined by Isabelle\<close>

theory Infsetsum
  imports "HOL-Analysis.Infinite_Set_Sum"
    Jordan_Normal_Form.Conjugate
    \<comment> \<open>\<^theory>\<open>Jordan_Normal_Form.Conjugate\<close> contains the instantiation \<open>complex :: ord\<close>.
               If we define our own instantiation, it would be impossible to load both
               \<^session>\<open>Jordan_Normal_Form\<close> and this theory.\<close>
begin

text \<open>This theory proves various facts about \<^const>\<open>infsetsum\<close>, the existing definition of 
  infinite sums in the Isabelle standard library. Those facts are not related to our new definition.\<close>

lemma 
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
  shows abs_summable_finiteI: "f abs_summable_on S"
  and infsetsum_finite_sets: "B \<ge> 0 \<Longrightarrow> norm (infsetsum f S) \<le> B"
proof -
  have main: "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B" if \<open>B \<ge> 0\<close> and \<open>S \<noteq> {}\<close>
  proof -
    define M normf where "M = count_space S" and "normf x = ennreal (norm (f x))" for x
    have "sum normf F \<le> ennreal B"
      if "finite F" and "F \<subseteq> S" and
        "\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> (\<Sum>i\<in>F. ennreal (norm (f i))) \<le> ennreal B" and
        "ennreal 0 \<le> ennreal B" for F
      using that unfolding normf_def[symmetric] by simp
    hence normf_B: "finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum normf F \<le> ennreal B" for F
      using assms[THEN ennreal_leI]
      by auto
    have "integral\<^sup>S M g \<le> B" if "simple_function M g" and "g \<le> normf" for g 
    proof -
      define gS where "gS = g ` S"
      have "finite gS"
        using that unfolding gS_def M_def simple_function_count_space by simp
      have "gS \<noteq> {}" unfolding gS_def using \<open>S \<noteq> {}\<close> by auto
      define part where "part r = g -` {r} \<inter> S" for r
      have r_finite: "r < \<infinity>" if "r : gS" for r 
        using \<open>g \<le> normf\<close> that unfolding gS_def le_fun_def normf_def apply auto
        using ennreal_less_top neq_top_trans top.not_eq_extremum by blast
      define B' where "B' r = (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)" for r
      have B'fin: "B' r < \<infinity>" for r
      proof -
        have "B' r \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)"
          unfolding B'_def
          by (metis (mono_tags, lifting) SUP_least SUP_upper)
        also have "\<dots> \<le> B"
          using normf_B unfolding part_def
          by (metis (no_types, lifting) Int_subset_iff SUP_least mem_Collect_eq)
        also have "\<dots> < \<infinity>"
          by simp
        finally show ?thesis by simp
      qed
      have sumB': "sum B' gS \<le> ennreal B + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        define N \<epsilon>N where "N = card gS" and "\<epsilon>N = \<epsilon> / N"
        have "N > 0" 
          unfolding N_def using \<open>gS\<noteq>{}\<close> \<open>finite gS\<close>
          by (simp add: card_gt_0_iff)
        from \<epsilon>N_def that have "\<epsilon>N > 0"
          by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_zero_less_divide)
        have c1: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and> finite y \<and> y \<subseteq> part r"
          if "B' r = 0" for r
          using that by auto
        have c2: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and> finite y \<and> y \<subseteq> part r" if "B' r \<noteq> 0" for r
        proof-
          have "B' r - \<epsilon>N < B' r"
            using B'fin \<open>0 < \<epsilon>N\<close> ennreal_between that by fastforce
          have "B' r - \<epsilon>N < Sup (sum normf ` {F. finite F \<and> F \<subseteq> part r}) \<Longrightarrow>
               \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and> finite F \<and> F \<subseteq> part r"
            by (metis (no_types, lifting) leD le_cases less_SUP_iff mem_Collect_eq)
          hence "B' r - \<epsilon>N < B' r \<Longrightarrow> \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and> finite F \<and> F \<subseteq> part r"
            by (subst (asm) (2) B'_def)
          then obtain F where "B' r - \<epsilon>N \<le> sum normf F" and "finite F" and "F \<subseteq> part r"
            using \<open>B' r - \<epsilon>N < B' r\<close> by auto  
          thus "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r"
            by (metis add.commute ennreal_minus_le_iff)
        qed
        have "\<forall>x. \<exists>y. B' x \<le> sum normf y + \<epsilon>N \<and>
            finite y \<and> y \<subseteq> part x"
          using c1 c2
          by blast 
        hence "\<exists>F. \<forall>x. B' x \<le> sum normf (F x) + \<epsilon>N \<and> finite (F x) \<and> F x \<subseteq> part x"
          by metis 
        then obtain F where F: "sum normf (F r) + \<epsilon>N \<ge> B' r" and Ffin: "finite (F r)" and Fpartr: "F r \<subseteq> part r" for r
          using atomize_elim by auto
        have w1: "finite gS"
          by (simp add: \<open>finite gS\<close>)          
        have w2: "\<forall>i\<in>gS. finite (F i)"
          by (simp add: Ffin)          
        have False
          if "\<And>r. F r \<subseteq> g -` {r} \<and> F r \<subseteq> S"
            and "i \<in> gS" and "j \<in> gS" and "i \<noteq> j" and "x \<in> F i" and "x \<in> F j"
          for i j x
          by (metis subsetD that(1) that(4) that(5) that(6) vimage_singleton_eq)          
        hence w3: "\<forall>i\<in>gS. \<forall>j\<in>gS. i \<noteq> j \<longrightarrow> F i \<inter> F j = {}"
          using Fpartr[unfolded part_def] by auto          
        have w4: "sum normf (\<Union> (F ` gS)) + \<epsilon> = sum normf (\<Union> (F ` gS)) + \<epsilon>"
          by simp
        have "sum B' gS \<le> (\<Sum>r\<in>gS. sum normf (F r) + \<epsilon>N)"
          using F by (simp add: sum_mono)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (\<Sum>r\<in>gS. \<epsilon>N)"
          by (simp add: sum.distrib)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (card gS * \<epsilon>N)"
          by auto
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + \<epsilon>"
          unfolding \<epsilon>N_def N_def[symmetric] using \<open>N>0\<close> 
          by (simp add: ennreal_times_divide mult.commute mult_divide_eq_ennreal)
        also have "\<dots> = sum normf (\<Union> (F ` gS)) + \<epsilon>" 
          using w1 w2 w3 w4
          by (subst sum.UNION_disjoint[symmetric])
        also have "\<dots> \<le> B + \<epsilon>"
          using \<open>finite gS\<close> normf_B add_right_mono Ffin Fpartr unfolding part_def
          by (simp add: \<open>gS \<noteq> {}\<close> cSUP_least)          
        finally show ?thesis
          by auto
      qed
      hence sumB': "sum B' gS \<le> B"
        using ennreal_le_epsilon ennreal_less_zero_iff by blast
      have "\<forall>r. \<exists>y. r \<in> gS \<longrightarrow> B' r = ennreal y"
        using B'fin less_top_ennreal by auto
      hence "\<exists>B''. \<forall>r. r \<in> gS \<longrightarrow> B' r = ennreal (B'' r)"
        by (rule_tac choice) 
      then obtain B'' where B'': "B' r = ennreal (B'' r)" if "r \<in> gS" for r
        by atomize_elim 
      have cases[case_names zero finite infinite]: "P" if "r=0 \<Longrightarrow> P" and "finite (part r) \<Longrightarrow> P"
        and "infinite (part r) \<Longrightarrow> r\<noteq>0 \<Longrightarrow> P" for P r
        using that by metis
      have emeasure_B': "r * emeasure M (part r) \<le> B' r" if "r : gS" for r
      proof (cases rule:cases[of r])
        case zero
        thus ?thesis by simp
      next
        case finite
        have s1: "sum g F \<le> sum normf F"
          if "F \<in> {F. finite F \<and> F \<subseteq> part r}"
          for F
          using \<open>g \<le> normf\<close> 
          by (simp add: le_fun_def sum_mono)

        have "r * of_nat (card (part r)) = r * (\<Sum>x\<in>part r. 1)" by simp
        also have "\<dots> = (\<Sum>x\<in>part r. r)"
          using mult.commute by auto
        also have "\<dots> = (\<Sum>x\<in>part r. g x)"
          unfolding part_def by auto
        also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum g F)"
          using finite
          by (simp add: Sup_upper)
        also have "\<dots> \<le> B' r"        
          unfolding B'_def
          using s1 SUP_subset_mono by blast
        finally have "r * of_nat (card (part r)) \<le> B' r" by assumption
        thus ?thesis
          unfolding M_def
          using part_def finite by auto
      next
        case infinite
        from r_finite[OF \<open>r : gS\<close>] obtain r' where r': "r = ennreal r'"
          using ennreal_cases by auto
        with infinite have "r' > 0"
          using ennreal_less_zero_iff not_gr_zero by blast
        obtain N::nat where N:"N > B / r'" and "real N > 0" apply atomize_elim
          using reals_Archimedean2
          by (metis less_trans linorder_neqE_linordered_idom)
        obtain F where "finite F" and "card F = N" and "F \<subseteq> part r"
          using infinite(1) infinite_arbitrarily_large by blast
        from \<open>F \<subseteq> part r\<close> have "F \<subseteq> S" unfolding part_def by simp
        have "B < r * N"
          unfolding r' ennreal_of_nat_eq_real_of_nat
          using N \<open>0 < r'\<close> \<open>B \<ge> 0\<close> r'
          by (metis enn2real_ennreal enn2real_less_iff ennreal_less_top ennreal_mult' less_le mult_less_cancel_left_pos nonzero_mult_div_cancel_left times_divide_eq_right)
        also have "r * N = (\<Sum>x\<in>F. r)"
          using \<open>card F = N\<close> by (simp add: mult.commute)
        also have "(\<Sum>x\<in>F. r) = (\<Sum>x\<in>F. g x)"
          using \<open>F \<subseteq> part r\<close>  part_def sum.cong subsetD by fastforce
        also have "(\<Sum>x\<in>F. g x) \<le> (\<Sum>x\<in>F. ennreal (norm (f x)))"
          by (metis (mono_tags, lifting) \<open>g \<le> normf\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> le_fun_def 
              sum_mono)
        also have "(\<Sum>x\<in>F. ennreal (norm (f x))) \<le> B"
          using \<open>F \<subseteq> S\<close> \<open>finite F\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> normf_B by blast 
        finally have "B < B" by auto
        thus ?thesis by simp
      qed

      have "integral\<^sup>S M g = (\<Sum>r \<in> gS. r * emeasure M (part r))"
        unfolding simple_integral_def gS_def M_def part_def by simp
      also have "\<dots> \<le> (\<Sum>r \<in> gS. B' r)"
        by (simp add: emeasure_B' sum_mono)
      also have "\<dots> \<le> B"
        using sumB' by blast
      finally show ?thesis by assumption
    qed
    hence int_leq_B: "integral\<^sup>N M normf \<le> B"
      unfolding nn_integral_def by (metis (no_types, lifting) SUP_least mem_Collect_eq)
    hence "integral\<^sup>N M normf < \<infinity>"
      using le_less_trans by fastforce
    hence "integrable M f"
      unfolding M_def normf_def by (rule integrableI_bounded[rotated], simp)
    hence v1: "f abs_summable_on S"
      unfolding abs_summable_on_def M_def by simp  

    have "(\<lambda>x. norm (f x)) abs_summable_on S"
      using v1 Infinite_Set_Sum.abs_summable_on_norm_iff[where A = S and f = f]
      by auto
    moreover have "0 \<le> norm (f x)"
      if "x \<in> S" for x
      by simp    
    moreover have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>count_space S) \<le> ennreal B"
      using M_def \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> int_leq_B by auto    
    ultimately have "ennreal (\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> ennreal B"
      by (simp add: nn_integral_conv_infsetsum)    
    hence v2: "(\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> B"
      by (subst ennreal_le_iff[symmetric], simp add: assms \<open>B \<ge> 0\<close>)
    show ?thesis
      using v1 v2 by auto
  qed

  from main
  show "f abs_summable_on S"
    by (metis abs_summable_on_finite assms empty_subsetI finite.emptyI sum_clauses(1))
  from main
  show \<open>0 \<le> B \<Longrightarrow> norm (infsetsum f S) \<le> B\<close>
    by (metis dual_order.trans finite.emptyI infsetsum_finite norm_infsetsum_bound sum.empty)
qed


lemma abs_summable_finiteI_converse:
  assumes f_sum_S: "f abs_summable_on S"
    and finite_F: "finite F" and FS: "F\<subseteq>S"
  defines "B \<equiv> (infsetsum (\<lambda>x. norm (f x)) S)"
  shows "sum (\<lambda>x. norm (f x)) F \<le> B"
  by (smt (verit, best) B_def FS abs_summable_on_normI abs_summable_on_subset f_sum_S finite_F infsetsum_cong infsetsum_finite infsetsum_mono_neutral_left norm_ge_zero)

lemma abs_summable_countable:
  fixes \<mu> :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes "\<mu> abs_summable_on T"
  shows "countable {x\<in>T. 0 \<noteq> \<mu> x}"
proof -
  define B where "B = infsetsum (\<lambda>x. norm (\<mu> x)) T"
  have \<mu>sum: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" if "finite F" and "F \<subseteq> T" for F
    unfolding B_def 
    using assms that abs_summable_finiteI_converse by auto
  define S where "S i = {x\<in>T. 1/real (Suc i) < norm (\<mu> x)}" for i::nat
  have "\<exists>i. x \<in> S i" if "0 < norm (\<mu> x)" and "x \<in> T" for x
    using that unfolding S_def
    by (metis (full_types, lifting) mem_Collect_eq nat_approx_posE)     
  hence union: "{x\<in>T. 0 < norm (\<mu> x)} = (\<Union>i. S i)"
    unfolding S_def by auto
  have finiteS: "finite (S i)" for i
  proof (rule ccontr)
    assume "infinite (S i)"
    then obtain F where F_Si: "F \<subseteq> S i" and cardF: "card F > (Suc i)*B" and finiteF: "finite F"
      by (metis One_nat_def ex_less_of_nat_mult infinite_arbitrarily_large lessI mult.commute mult.left_neutral of_nat_0_less_iff of_nat_1)
    from F_Si have F_T: "F \<subseteq> T" 
      unfolding S_def by blast
    from finiteF \<mu>sum F_T have sumF: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" by simp
    have "1 / real (Suc i) \<le> norm (\<mu> x)"
      if "x \<in> F"
      for x
      using that F_Si S_def by auto
    hence "sum (\<lambda>x. norm (\<mu> x)) F \<ge> sum (\<lambda>_. 1/real (Suc i)) F" (is "_ \<ge> \<dots>")
      using sum_mono
      by metis       
    moreover have "\<dots> = real (card F) / (Suc i)"
      by (subst sum_constant_scale, auto)
    moreover have "\<dots> > B"
      using cardF
      by (simp add: linordered_field_class.mult_imp_less_div_pos algebra_simps)
    ultimately have "sum (\<lambda>x. norm (\<mu> x)) F > B"
      by linarith 
    with sumF show False by simp
  qed

  have "countable (S i)"
    if "i \<in> UNIV"
    for i
    using finiteS by (simp add: countable_finite)
  hence "countable (\<Union>i. S i)"
    using countable_UN by simp
  hence "countable {x\<in>T. 0 < norm (\<mu> x)}"
    unfolding union by simp
  thus ?thesis
    by simp
qed

lemma infsetsum_cnj[simp]: "infsetsum (\<lambda>x. cnj (f x)) M = cnj (infsetsum f M)"
  unfolding infsetsum_def by (rule integral_cnj)

lemma infsetsum_Re: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Re (f x)) M = Re (infsetsum f M)"
  unfolding infsetsum_def 
  using integral_Re assms by (simp add: abs_summable_on_def)

lemma infsetsum_Im: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Im (f x)) M = Im (infsetsum f M)"
  unfolding infsetsum_def using assms by (simp add: abs_summable_on_def)

lemma infsetsum_mono_complex:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f abs_summable_on A" and g_sum: "g abs_summable_on A"
  assumes x: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsetsum f A \<le> infsetsum g A"
proof -
  have a1: "infsetsum f A = Complex (Re (infsetsum f A)) (Im (infsetsum f A))" by auto
  also have a2: "Re (infsetsum f A) = infsetsum (\<lambda>x. Re (f x)) A"
    unfolding infsetsum_def 
    using assms by (simp add: abs_summable_on_def)
  also have a3: "Im (infsetsum f A) = infsetsum (\<lambda>x. Im (f x)) A"
    using f_sum by (rule infsetsum_Im[symmetric])
  finally have fsplit: "infsetsum f A = Complex (\<Sum>\<^sub>ax\<in>A. Re (f x)) (\<Sum>\<^sub>ax\<in>A. Im (f x))" by assumption
  have "infsetsum g A = Complex (Re (infsetsum g A)) (Im (infsetsum g A))" by auto
  also have b2: "Re (infsetsum g A) = infsetsum (\<lambda>x. Re (g x)) A"
    using g_sum by (rule infsetsum_Re[symmetric])
  also have b1: "Im (infsetsum g A) = infsetsum (\<lambda>x. Im (g x)) A "
    using g_sum by (rule infsetsum_Im[symmetric])
  finally have gsplit: "infsetsum g A = Complex (\<Sum>\<^sub>ax\<in>A. Re (g x)) (\<Sum>\<^sub>ax\<in>A. Im (g x))" 
    by assumption
  have Re_leq: "Re (f x) \<le> Re (g x)" if "x\<in>A" for x
    using that assms unfolding less_eq_complex_def by simp
  have Im_eq: "Im (f x) = Im (g x)" if "x\<in>A" for x
    using that assms 
    unfolding less_eq_complex_def by simp
  have Refsum: "(\<lambda>x. Re (f x)) abs_summable_on A"
    using assms(1) abs_Re_le_cmod by (simp add: abs_summable_on_comparison_test[where g=f])
  have Regsum: "(\<lambda>x. Re (g x)) abs_summable_on A"
    using assms(2) abs_Re_le_cmod 
    by (simp add: abs_summable_on_comparison_test[where g=g])
  show "infsetsum f A \<le> infsetsum g A"
    unfolding fsplit gsplit
      by (smt (verit, ccfv_SIG) Im_eq Re_leq Refsum Regsum a2 a3 b1 b2 fsplit gsplit infsetsum_cong infsetsum_mono less_eq_complex_def)
qed

lemma infsetsum_subset_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))
  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    using assms fBA infsetsum_mono_complex
    by (metis DiffD2 abs_summable_on_0)
  also have "... = infsetsum f B - infsetsum f A"
    using assms by (simp add: infsetsum_Diff)
  finally show ?thesis by auto
qed

lemma infsetsum_subset_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))
  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    using assms fBA 
    by (metis DiffD2 calculation infsetsum_nonneg) 
  also have "... = infsetsum f B - infsetsum f A"
    using assms by (simp add: infsetsum_Diff)
  finally show ?thesis by auto
qed

lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule abs_summable_finiteI)
  have aux: "a\<le>a' \<Longrightarrow> b\<le>b' \<Longrightarrow> a+b \<le> a'+b'" for a b a' b' :: real by simp
  fix F assume r1: "finite F" and b4: "F \<subseteq> A"
  define B :: real where "B = (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))"

  have a1: "(\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i))"
    apply (rule infsetsum_mono_neutral_left)
    by (auto simp: r1 x2_sum b4)
  have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
    unfolding norm_mult
    by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
  hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm (x i * x i) + norm (y i * y i))"
    by (simp add: sum_mono)
  also have "\<dots> = (\<Sum>i\<in>F. norm (x i * x i)) + (\<Sum>i\<in>F. norm (y i * y i))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>F. norm (y i * y i))"
    by (simp add: \<open>finite F\<close>)
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))" 
    using aux a1
    by (simp add: aux \<open>F \<subseteq> A\<close> \<open>finite F\<close> abs_summable_finiteI_converse x2_sum y2_sum)
  also have "\<dots> = B"
    unfolding B_def by simp
  finally show "(\<Sum>i\<in>F. norm (x i * y i)) \<le> B" by assumption
qed

lemma abs_summable_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
proof
  show "f abs_summable_on A"
    if "(\<lambda>i. cnj (f i)) abs_summable_on A"
    using that abs_summable_on_norm_iff[symmetric]
      abs_summable_on_comparison_test by fastforce    
  show "(\<lambda>i. cnj (f i)) abs_summable_on A"
    if "f abs_summable_on A"
    using that abs_summable_on_norm_iff[symmetric]
      abs_summable_on_comparison_test by fastforce 
qed

lemma infsetsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof -
  have sum_F_A: "sum f F \<le> infsetsum f A" 
    if "F \<in> {F. finite F \<and> F \<subseteq> A}" 
    for F
  proof-
    from that have "finite F" and "F \<subseteq> A" by auto
    from \<open>finite F\<close> have "sum f F = infsetsum f F" by auto
    also have "\<dots> \<le> infsetsum f A"
    proof (rule infsetsum_mono_neutral_left)
      show "f abs_summable_on F"
        by (simp add: \<open>finite F\<close>)        
      show "f abs_summable_on A"
        by (simp add: local.summable)        
      show "f x \<le> f x"
        if "x \<in> F"
        for x :: 'a
        by simp 
      show "F \<subseteq> A"
        by (simp add: \<open>F \<subseteq> A\<close>)        
      show "0 \<le> f x"
        if "x \<in> A - F"
        for x :: 'a
        using that fnn by auto 
    qed
    finally show ?thesis by assumption
  qed 
  hence geq: "ennreal (infsetsum f A) \<ge> (SUP F\<in>{G. finite G \<and> G \<subseteq> A}. (ennreal (sum f F)))"
    by (meson SUP_least ennreal_leI)

  define fe where "fe x = ennreal (f x)" for x

  have sum_f_int: "infsetsum f A = \<integral>\<^sup>+ x. fe x \<partial>(count_space A)"
    unfolding infsetsum_def fe_def
  proof (rule nn_integral_eq_integral [symmetric])
    show "integrable (count_space A) f"
      using abs_summable_on_def local.summable by blast      
    show "AE x in count_space A. 0 \<le> f x"
      using fnn by auto      
  qed
  also have "\<dots> = (SUP g \<in> {g. finite (g`A) \<and> g \<le> fe}. integral\<^sup>S (count_space A) g)"
    unfolding nn_integral_def simple_function_count_space by simp
  also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
  proof (rule Sup_least)
    fix x assume "x \<in> integral\<^sup>S (count_space A) ` {g. finite (g ` A) \<and> g \<le> fe}"
    then obtain g where xg: "x = integral\<^sup>S (count_space A) g" and fin_gA: "finite (g`A)" 
      and g_fe: "g \<le> fe" by auto
    define F where "F = {z:A. g z \<noteq> 0}"
    hence "F \<subseteq> A" by simp

    have fin: "finite {z:A. g z = t}" if "t \<noteq> 0" for t
    proof (rule ccontr)
      assume inf: "infinite {z:A. g z = t}"
      hence tgA: "t \<in> g ` A"
        by (metis (mono_tags, lifting) image_eqI not_finite_existsD)
      have "x = (\<Sum>x \<in> g ` A. x * emeasure (count_space A) (g -` {x} \<inter> A))"
        unfolding xg simple_integral_def space_count_space by simp
      also have "\<dots> \<ge> (\<Sum>x \<in> {t}. x * emeasure (count_space A) (g -` {x} \<inter> A))" (is "_ \<ge> \<dots>")
      proof (rule sum_mono2)
        show "finite (g ` A)"
          by (simp add: fin_gA)          
        show "{t} \<subseteq> g ` A"
          by (simp add: tgA)          
        show "0 \<le> b * emeasure (count_space A) (g -` {b} \<inter> A)"
          if "b \<in> g ` A - {t}"
          for b :: ennreal
          using that
          by simp
      qed
      also have "\<dots> = t * emeasure (count_space A) (g -` {t} \<inter> A)"
        by auto
      also have "\<dots> = t * \<infinity>"
      proof (subst emeasure_count_space_infinite)
        show "g -` {t} \<inter> A \<subseteq> A"
          by simp             
        have "{a \<in> A. g a = t} = {a \<in> g -` {t}. a \<in> A}"
          by auto
        thus "infinite (g -` {t} \<inter> A)"
          by (metis (full_types) Int_def inf) 
        show "t * \<infinity> = t * \<infinity>"
          by simp
      qed
      also have "\<dots> = \<infinity>" using \<open>t \<noteq> 0\<close>
        by (simp add: ennreal_mult_eq_top_iff)
      finally have x_inf: "x = \<infinity>"
        using neq_top_trans by auto
      have "x = integral\<^sup>S (count_space A) g" by (fact xg)
      also have "\<dots> = integral\<^sup>N (count_space A) g"
        by (simp add: fin_gA nn_integral_eq_simple_integral)
      also have "\<dots> \<le> integral\<^sup>N (count_space A) fe"
        using g_fe
        by (simp add: le_funD nn_integral_mono)
      also have "\<dots> < \<infinity>"
        by (metis sum_f_int ennreal_less_top infinity_ennreal_def) 
      finally have x_fin: "x < \<infinity>" by simp
      from x_inf x_fin show False by simp
    qed
    have F: "F = (\<Union>t\<in>g`A-{0}. {z\<in>A. g z = t})"
      unfolding F_def by auto
    hence "finite F"
      unfolding F using fin_gA fin by auto
    have "x = integral\<^sup>N (count_space A) g"
      unfolding xg
      by (simp add: fin_gA nn_integral_eq_simple_integral)
    also have "\<dots> = set_nn_integral (count_space UNIV) A g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = set_nn_integral (count_space UNIV) F g"
    proof -
      have "\<forall>a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) = g a * (if a \<in> A then 1 else 0)"
        by auto
      hence "(\<integral>\<^sup>+ a. g a * (if a \<in> A then 1 else 0) \<partial>count_space UNIV)
           = (\<integral>\<^sup>+ a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) \<partial>count_space UNIV)"
        by presburger
      thus ?thesis unfolding F_def indicator_def
        using mult.right_neutral mult_zero_right nn_integral_cong
        by blast
    qed
    also have "\<dots> = integral\<^sup>N (count_space F) g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = sum g F" 
      using \<open>finite F\<close> by (rule nn_integral_count_space_finite)
    also have "sum g F \<le> sum fe F"
      using g_fe unfolding le_fun_def
      by (simp add: sum_mono) 
    also have "\<dots> \<le> (SUP F \<in> {G. finite G \<and> G \<subseteq> A}. (sum fe F))"
      using \<open>finite F\<close> \<open>F\<subseteq>A\<close>
      by (simp add: SUP_upper)
    also have "\<dots> = (SUP F \<in> {F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    proof (rule SUP_cong [OF refl])
      have "finite x \<Longrightarrow> x \<subseteq> A \<Longrightarrow> (\<Sum>x\<in>x. ennreal (f x)) = ennreal (sum f x)"
        for x
        by (metis fnn subsetCE sum_ennreal)
      thus "sum fe x = ennreal (sum f x)"
        if "x \<in> {G. finite G \<and> G \<subseteq> A}"
        for x :: "'a set"
        using that unfolding fe_def by auto      
    qed 
    finally show "x \<le> \<dots>" by simp
  qed
  finally have leq: "ennreal (infsetsum f A) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    by assumption
  from leq geq show ?thesis by simp
qed


lemma infsetsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have "ereal (infsetsum f A) = enn2ereal (ennreal (infsetsum f A))"
    by (simp add: fnn infsetsum_nonneg)
  also have "\<dots> = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
  proof (subst infsetsum_nonneg_is_SUPREMUM_ennreal)
    show "f abs_summable_on A"
      by (simp add: local.summable)      
    show "0 \<le> f x"
      if "x \<in> A"
      for x :: 'a
      using that
      by (simp add: fnn) 
    show "enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F)) = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
      by simp      
  qed    
  also have "\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
  proof (simp add: image_def Sup_ennreal.rep_eq)
    have "0 \<le> Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x = ennreal (sum f xa)) \<and>
                     y = enn2ereal x}"
      by (metis (mono_tags, lifting) Sup_upper empty_subsetI ennreal_0 finite.emptyI
          mem_Collect_eq sum.empty zero_ennreal.rep_eq)
    moreover have "Sup {y. \<exists>x. (\<exists>y. finite y \<and> y \<subseteq> A \<and> x = ennreal (sum f y)) \<and>
                y = enn2ereal x} = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      using enn2ereal_ennreal fnn in_mono sum_nonneg Collect_cong
      by smt (* > 1s *)
    ultimately show "max 0 (Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x
                                       = ennreal (sum f xa)) \<and> y = enn2ereal x})
         = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      by linarith
  qed   
  finally show ?thesis
    by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
proof -
  have "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
    using assms by (rule infsetsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
  proof (subst ereal_SUP)
    show "\<bar>SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a)\<bar> \<noteq> \<infinity>"
      using calculation by fastforce      
    show "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f F)) = (SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a))"
      by simp      
  qed
  finally show ?thesis by simp
qed

lemma infsetsum_geq0_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum f M \<ge> 0" (is "?lhs \<ge> _")
proof -
  have "?lhs \<ge> infsetsum (\<lambda>x. 0) M" (is "_ \<ge> \<dots>")
  proof (rule infsetsum_mono_complex)
    show "(\<lambda>x. 0::complex) abs_summable_on M"
      by simp      
    show "f abs_summable_on M"
      by (simp add: assms(1))      
    show "0 \<le> f x"
      if "x \<in> M"
      for x :: 'a
      using that
      using fnn by blast
  qed
  also have "\<dots> = 0"
    by auto
  finally show ?thesis by assumption
qed

lemma infsetsum_cmod:
  assumes "f abs_summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum (\<lambda>x. cmod (f x)) M = cmod (infsetsum f M)"
proof -
  have nn: "infsetsum f M \<ge> 0" 
    using assms by (rule infsetsum_geq0_complex) 
  have "infsetsum (\<lambda>x. cmod (f x)) M = infsetsum (\<lambda>x. Re (f x)) M"
    using fnn cmod_eq_Re less_eq_complex_def by auto
  also have "\<dots> = Re (infsetsum f M)"
    using assms(1) infsetsum_Re by blast
  also have "\<dots> = cmod (infsetsum f M)" using nn cmod_eq_Re less_eq_complex_def by auto
  finally show ?thesis by assumption
qed

text \<open>The following lemma is a strengthening of @{thm infsetsum_Sigma}.
  It does not require \<^term>\<open>A\<close> and \<^term>\<open>B\<close> to be countable.\<close>

lemma infsetsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "f abs_summable_on (Sigma A B)"
  shows "infsetsum f (Sigma A B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from summable have countable_Sigma: "countable {x \<in> Sigma A B. 0 \<noteq> f x}"
    by (rule abs_summable_countable)
  define A' where "A' = fst ` {x \<in> Sigma A B. 0 \<noteq> f x}"
  have countA': "countable A'"
    using countable_Sigma unfolding A'_def by auto

  define B' where "B' a = snd ` ({x \<in> Sigma A B. 0 \<noteq> f x} \<inter> {(a,b) | b. True})" for a
  have countB': "countable (B' a)" for a
    using countable_Sigma unfolding B'_def by auto

  have Sigma_eq: "x \<in> Sigma A B \<longleftrightarrow> x \<in> Sigma A' B'" if "f x \<noteq> 0" for x
    unfolding A'_def B'_def Sigma_def 
    using that by force

  have Sigma'_smaller: "Sigma A' B' \<subseteq> Sigma A B"
    unfolding A'_def B'_def by auto
  with summable have summable': "f abs_summable_on Sigma A' B'"
    using abs_summable_on_subset by blast

  have A'_smaller: "A' \<subseteq> A"
    unfolding A'_def by auto
  have B'_smaller: "B' a \<subseteq> B a" for a
    unfolding B'_def by auto

  have "infsetsum f (Sigma A B) = infsetsum f (Sigma A' B')"
    apply (rule infsetsum_cong_neutral)
    using Sigma_eq by auto
  also from countA' countB' summable' have "\<dots> = (\<Sum>\<^sub>aa\<in>A'. \<Sum>\<^sub>ab\<in>B' a. f (a, b))"
    by (rule infsetsum_Sigma)
  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B' a. f (a, b))" (is "_ = (\<Sum>\<^sub>aa\<in>A. ?inner a)" is "_ = ?rhs")
    apply (rule infsetsum_cong_neutral)
    using A'_smaller  apply auto
    by (meson B'_smaller SigmaD1 SigmaI Sigma_eq infsetsum_all_0 subset_eq)
  also have "?inner a = (\<Sum>\<^sub>ab\<in>B a. f (a, b))" if "a\<in>A" for a
    apply (rule infsetsum_cong_neutral)
    using B'_smaller Sigma_eq \<open>a \<in> A\<close> by auto
  hence "?rhs = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. f (a, b))"
    by (rule infsetsum_cong, auto)
  finally show ?thesis 
    by simp
qed

text \<open>The following lemma is a strengthening of @{thm infsetsum_Sigma'}.
  It does not require \<^term>\<open>A\<close> and \<^term>\<open>B\<close> to be countable.\<close>

lemma infsetsum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (Sigma A B)"
  shows "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) A = infsetsum (\<lambda>(x,y). f x y) (Sigma A B)"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on A \<times> B"
  shows "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
proof-
  from summable have summable': "(\<lambda>(x,y). f y x) abs_summable_on B \<times> A"
    by (subst abs_summable_on_Times_swap) auto
  have bij: "bij_betw (\<lambda>(x, y). (y, x)) (B \<times> A) (A \<times> B)"
    by (auto simp: bij_betw_def inj_on_def)
  have "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
    using summable by (subst infsetsum_Sigma) auto
  also have "\<dots> = infsetsum (\<lambda>(x,y). f y x) (B \<times> A)"
    by (subst infsetsum_reindex_bij_betw[OF bij, of "\<lambda>(x,y). f x y", symmetric])
      (simp_all add: case_prod_unfold)
  also have "\<dots> = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
    using summable' by (subst infsetsum_Sigma) auto
  finally show ?thesis.
qed

lemma abs_summable_partition:
  fixes T :: "'b set" and I :: "'a set"
  assumes "\<And>i. f abs_summable_on S i"
  and "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on I"
  and "T \<subseteq> (\<Union>i\<in>I. S i)"
  shows "f abs_summable_on T"
proof (rule abs_summable_finiteI)
  fix F assume finite_F: "finite F" and FT: "F \<subseteq> T"
  define index where "index s = (SOME i. i\<in>I \<and> s\<in>S i)" for s
  hence index_I: "index s \<in> I" and S_index: "s \<in> S (index s)" if "s \<in> (\<Union>i\<in>I. S i)" for s
  proof auto
    show "(SOME i. i \<in> I \<and> s \<in> S i) \<in> I"
      if "\<And>s. index s = (SOME i. i \<in> I \<and> s \<in> S i)"
      using that
      by (metis (no_types, lifting) UN_iff \<open>s \<in> \<Union> (S ` I)\<close> someI_ex) 
    show "s \<in> S (SOME i. i \<in> I \<and> s \<in> S i)"
      if "\<And>s. index s = (SOME i. i \<in> I \<and> s \<in> S i)"
      using that
      by (metis (no_types, lifting) UN_iff \<open>s \<in> \<Union> (S ` I)\<close> someI_ex) 
  qed
  define S' where "S' i = {s\<in>S i. i = index s}" for i
  have S'_S: "S' i \<subseteq> S i" for i
    unfolding S'_def by simp
  hence f_sum_S': "f abs_summable_on S' i" for i
    by (meson abs_summable_on_subset assms(1))
  with assms(1) S'_S have "(\<Sum>\<^sub>ax\<in>S' i. norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>S i. norm (f x))" for i
    by (simp add: infsetsum_mono_neutral_left)
  with assms(2) have sum_I: "(\<lambda>i. \<Sum>\<^sub>ax\<in>S' i. norm (f x)) abs_summable_on I"
    by (smt abs_summable_on_comparison_test' infsetsum_cong norm_ge_zero norm_infsetsum_bound real_norm_def)
  have "(\<Union>i\<in>I. S i) = (\<Union>i\<in>I. S' i)"
    unfolding S'_def by (auto intro!: index_I S_index)
  with assms(3) have T_S': "T \<subseteq> (\<Union>i\<in>I. S' i)"
    by simp
  have S'_disj: "(S' i) \<inter> (S' j) = {}" if "i\<noteq>j" for i j
    unfolding S'_def disjnt_def using that by auto

  define B where "B i = (\<Sum>\<^sub>ax\<in>S i. norm (f x))" for i
  have sum_FS'_B: "(\<Sum>x\<in>F\<inter>S' i. norm (f x)) \<le> B i" for i
    unfolding B_def using f_sum_S' finite_F FT
    by (metis S'_S abs_summable_finiteI_converse assms(1) finite_Int le_inf_iff order_refl 
        subset_antisym)
  have B_pos[simp]: "B i \<ge> 0" for i
    unfolding B_def by (rule infsetsum_nonneg, simp)
  have B_sum_I[simp]: "B abs_summable_on I"
    by (simp add: B_def assms(2))
  define J where "J = {i\<in>I. F\<inter>S' i \<noteq> {}}"
  have finite_J[simp]: "finite J"
  proof -
    define a where "a i = (SOME x. x\<in>F\<inter>S' i)" for i
    hence a: "a i \<in> F\<inter>S' i" if "i \<in> J" for i
      unfolding J_def
      by (metis (mono_tags) Collect_conj_eq Int_Collect J_def some_in_eq that)
    have xy: "x = y"
      if "x \<in> J" and "y \<in> J" and "a x = a y" and "\<And>i. i \<in> J \<Longrightarrow> a i \<in> F \<and> a i \<in> S' i"
           and "\<And>i j. i \<noteq> j \<Longrightarrow> S' i \<inter> S' j = {}"
         for x y     
      using that a S'_disj
      by (metis S'_disj disjoint_iff_not_equal)
    hence "inj_on a J"
      unfolding inj_on_def
      using S'_disj a by auto 
    moreover have "a ` J \<subseteq> F"
      using a by auto
    ultimately show "finite J"
      using finite_F Finite_Set.inj_on_finite by blast
  qed
  have JI[simp]: "J \<subseteq> I"
    unfolding J_def by simp
  have "F = (\<Union>i\<in>J. F\<inter>S' i)"
    unfolding J_def apply auto
    by (metis FT T_S' UN_E disjoint_iff_not_equal subsetD)
  hence "(\<Sum>x\<in>F. norm (f x)) = (\<Sum>x\<in>(\<Union>i\<in>J. F\<inter>S' i). norm (f x))"
    by simp
  also have "\<dots> = (\<Sum>i\<in>J. \<Sum>x\<in>F \<inter> S' i. norm (f x))"
    apply (rule sum.UNION_disjoint)
    using S'_disj finite_F by auto
  also have "\<dots> \<le> (\<Sum>i\<in>J. B i)"
    using sum_FS'_B
    by (simp add: ordered_comm_monoid_add_class.sum_mono)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>J. B i)"
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
    apply (rule infsetsum_mono_neutral_left)
    by auto   
  finally show "(\<Sum>x\<in>F. norm(f x)) \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
    by simp
qed

lemma abs_summable_product':
  fixes X :: "'a set" and Y :: "'b set"
  assumes "\<And>x. (\<lambda>y. f (x,y)) abs_summable_on Y"
    and "(\<lambda>x. \<Sum>\<^sub>ay\<in>Y. norm (f (x,y))) abs_summable_on X"
  shows "f abs_summable_on X\<times>Y"
proof-
  define S where "S x = {x} \<times> Y" for x :: 'a
  have bij[simp]: "bij_betw (Pair x) Y (S x)" for x
    apply (rule bij_betwI [where g = snd])
    using S_def by auto
  have "f abs_summable_on S x" for x
  proof (subst abs_summable_on_reindex_bij_betw [symmetric , where A = Y and g = "\<lambda>y. (x,y)"])
    show "bij_betw (Pair x) Y (S x)"
      by simp      
    show "(\<lambda>xa. f (x, xa)) abs_summable_on Y"
      using assms(1) by auto      
  qed
  moreover have "bij_betw (Pair x) Y (S x)"
    for x
    unfolding S_def using bij_betw_def
    using S_def bij by auto
  hence "(\<Sum>\<^sub>ay\<in>Y. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>S x. norm (f y))" for x
    by (rule infsetsum_reindex_bij_betw) 
  hence "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    using assms(2) by simp
  hence "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    by auto
  moreover have "X \<times> Y \<subseteq> (\<Union>i\<in>X. S i)"
    unfolding S_def by auto
  ultimately show ?thesis
    by (rule abs_summable_partition[where S=S and I=X])
qed

lemma infsetsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A"
    and summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
proof-
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f x y}" for x
  have B'_B[simp]: "B' x \<subseteq> B x" for x
    unfolding B'_def by simp
  have PiE_subset: "Pi\<^sub>E A B' \<subseteq> Pi\<^sub>E A B"
    by (simp add: PiE_mono)
  have "f x abs_summable_on B x" if "x\<in>A" for x
    using that
    by (simp add: local.summable) 
  hence countable: "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def using abs_summable_countable
    using that by blast
  have summable: "f x abs_summable_on B' x" if "x\<in>A" for x
    using that summable[where x = x] \<open>\<And>x. B' x \<subseteq> B x\<close> abs_summable_on_subset by blast
  have 0: "(\<Prod>x\<in>A. f x (g x)) = 0" if "g \<in> Pi\<^sub>E A B - Pi\<^sub>E A B'" for g
  proof-
    from that have "g \<in> extensional A"
      by (simp add: PiE_def)
    from that have "g \<notin> Pi\<^sub>E A B'"
      by simp
    with \<open>g \<in> extensional A\<close> have "g \<notin> Pi A B'"
      unfolding PiE_def by simp
    then obtain x where "x\<in>A" and "g x \<notin> B' x"
      unfolding Pi_def by auto
    hence "f x (g x) = 0"
      unfolding B'_def using that by auto
    with finite show ?thesis
      apply (rule_tac prod_zero)
      using  \<open>x \<in> A\<close> by auto
  qed

  have d: "infsetsum (f x) (B' x) = infsetsum (f x) (B x)" if "x \<in> A" for x
    apply (rule infsetsum_cong_neutral)
    by (auto simp: B'_def)
  have "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B)
      = infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B')"
    apply (rule infsetsum_cong_neutral)
    using 0 PiE_subset by auto
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B' x))"
    using finite countable summable by (rule infsetsum_prod_PiE)
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
    using d
    by auto
  finally show ?thesis.
qed


lemma infsetsum_0D:
  fixes f :: "'a \<Rightarrow> real"
  assumes "infsetsum f A = 0"
  and abs_sum: "f abs_summable_on A"
  and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  and "x \<in> A"
  shows "f x = 0"
proof -
  from abs_sum have [simp]: "f abs_summable_on (A-{x})"
    by (meson Diff_subset abs_summable_on_subset)
  from abs_sum \<open>x\<in>A\<close> have [simp]: "f abs_summable_on {x}"
    by auto
  have a: "\<And>a. a \<in> A - {x} \<Longrightarrow> a \<in> A"
    by simp   
  from assms have "0 = infsetsum f A"
    by simp
  also have "\<dots> = infsetsum f (A-{x}) + infsetsum f {x}"
    apply (subst infsetsum_Un_disjoint [symmetric])
    apply auto
    using assms(4) insert_Diff by fastforce      
  also have "\<dots> \<ge> 0 + infsetsum f {x}" (is "_ \<ge> \<dots>")
    using a
    by (smt infsetsum_nonneg nneg)    
  also have "\<dots> = f x"
    by simp
  finally have "f x \<le> 0".
  with nneg[OF \<open>x\<in>A\<close>] show "f x = 0"
    by auto
qed

lemma infsetsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology, division_ring}"
  shows  "infsetsum (\<lambda>x. f x * c) A = infsetsum f A * c"
proof (cases "c \<noteq> 0 \<longrightarrow> f abs_summable_on A")
  case True
  have "(\<Sum>\<^sub>ax\<in>A. f x * c) = infsetsum f A * c"
    if "f abs_summable_on A"
    using infsetsum_cmult_left that by blast
  thus ?thesis
    using True by auto     
next
  case False
  hence "c\<noteq>0" and "\<not> f abs_summable_on A"
    by auto
  have "\<not> (\<lambda>x. f x * c) abs_summable_on A"
  proof (rule notI)
    assume "(\<lambda>x. f x * c) abs_summable_on A"
    hence "(\<lambda>x. (f x * c) * inverse c) abs_summable_on A"
      by (rule abs_summable_on_cmult_left)
    with \<open>\<not> f abs_summable_on A\<close> show False
      by (metis (no_types, lifting) False Groups.mult_ac(1) abs_summable_on_cong mult_1_right
          right_inverse)
  qed
  with \<open>\<not> f abs_summable_on A\<close>
  show ?thesis 
    by (simp add: not_summable_infsetsum_eq)
qed

lemma abs_summable_on_zero_diff:
  assumes "f abs_summable_on A"
  and "\<And>x. x \<in> B - A \<Longrightarrow> f x = 0"
  shows "f abs_summable_on B"
proof (subst asm_rl [of "B = (B-A) \<union> (A\<inter>B)"])
  show "B = B - A \<union> A \<inter> B"
    by auto
  have "(\<lambda>x. 0::real) abs_summable_on B - A"
    by simp    
  moreover have "norm (f x) \<le> 0" if "x \<in> B - A" for x :: 'a
    using that by (simp add: assms(2)) 
  ultimately have "f abs_summable_on B - A"
    by (rule abs_summable_on_comparison_test' [where g = "\<lambda>x. 0"])   
  moreover have "f abs_summable_on A \<inter> B"
      using abs_summable_on_subset assms(1) by blast
  ultimately show "f abs_summable_on B - A \<union> A \<inter> B"
    by (rule abs_summable_on_union)    
qed

lemma abs_summable_on_Sigma_iff:
  "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof auto
  assume sum_AB: "f abs_summable_on Sigma A B"
  define S' where "S' = {x\<in>Sigma A B. 0 \<noteq> f x}"
  from sum_AB have "countable S'"
    unfolding S'_def by (rule abs_summable_countable)
  define A' B' where "A' = fst ` S'" and "B' x = B x \<inter> snd ` S'" for x
  have A'A: \<open>A' \<subseteq> A\<close> and B'B: \<open>B' x \<subseteq> B x\<close> for x
    unfolding A'_def B'_def S'_def by auto
  have  cntA: "countable A'" and cntB: "countable (B' x)" for x
    unfolding A'_def B'_def using \<open>countable S'\<close> by auto
  have f0: "f (x,y) = 0" if "x \<in> A - A'" and "y \<in> B x" for x y
  proof -
    from that have "(x,y) \<in> Sigma A B"
      by auto
    moreover from that have "(x,y) \<notin> S'"
      unfolding A'_def
      by (metis image_eqI mem_simps(6) prod.sel(1)) 
    ultimately show "f (x,y) = 0"
      unfolding S'_def by auto
  qed
  have f0': "f (x,y) = 0" if "x \<in> A" and "y \<in> B x - B' x" for x y
  proof -
    from that have "(x,y) \<in> Sigma A B"
      by auto
    moreover from that have "(x,y) \<notin> S'"
      unfolding B'_def
      by (auto simp add: rev_image_eqI)
    ultimately show "f (x,y) = 0"
      unfolding S'_def by auto
  qed
  have "Sigma A' B' \<subseteq> Sigma A B"
    using A'A B'B by (rule Sigma_mono)
  hence sum_A'B': "f abs_summable_on Sigma A' B'"
    using sum_AB abs_summable_on_subset by auto 
  from sum_A'B' have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A'" for x
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] that by auto
  moreover have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A - A'" for x
    apply (rule abs_summable_on_zero_diff [where A = "{}"])
    using that f0 that B'B by auto
  ultimately have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A" for x
    using that by auto
  thus "(\<lambda>y. f (x, y)) abs_summable_on B x" if "x \<in> A" for x
    apply (rule abs_summable_on_zero_diff)
    using that f0' by auto

  have Q: "\<And>x. x \<in> A - A' \<Longrightarrow> (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) = 0"
    apply (subst infsetsum_cong[where g=\<open>\<lambda>x. 0\<close> and B="B' _"])
    using f0 B'B by auto

  from sum_A'B' have "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A'"
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] by auto
  hence "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A"
    apply (rule abs_summable_on_zero_diff)
    using Q by auto
  have R: "\<And>x. x \<in> A \<Longrightarrow>
         (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) =
         (\<Sum>\<^sub>ay\<in>B x. norm (f (x, y)))"
    apply (rule infsetsum_cong_neutral)
    using B'B f0' by auto
  thus "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A"    
    using \<open>(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A\<close> by auto 
next
  assume sum_B: "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
  assume sum_A: "(\<lambda>x. \<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) abs_summable_on A"
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f (x,y)}" for x
  from sum_B have cnt_B': "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def apply (rule_tac abs_summable_countable)
    using that by auto
  define A' where "A' = {x\<in>A. 0 \<noteq> (\<Sum>\<^sub>ay\<in>B x. norm (f (x, y)))}"
  from sum_A have cnt_A': "countable A'"
    unfolding A'_def by (rule abs_summable_countable)
  have A'A: "A' \<subseteq> A" and B'B: "B' x \<subseteq> B x" for x
    unfolding A'_def B'_def by auto
  have f0': "f (x,y) = 0" if (* "x \<in> A" and *) "y \<in> B x - B' x" for x y
    using that unfolding B'_def by auto
  have f0: "f (x,y) = 0" if "x \<in> A - A'" and "y \<in> B x" for x y
  proof -
    have "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = 0"
      using that unfolding A'_def by auto
    hence "norm (f (x, y)) = 0"
      apply (rule infsetsum_0D)
      using sum_B that by auto
    thus ?thesis
      by auto
  qed

  from sum_B have sum_B': "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x\<in>A" for x
  proof (rule_tac abs_summable_on_subset [where B = "B x"])
    show "(\<lambda>y. f (x, y)) abs_summable_on B x"
      if "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
      using that \<open>x \<in> A\<close> by blast 
    show "B' x \<subseteq> B x"
      if "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
      using that
      by (simp add: B'B) 
  qed
  have *: "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y)))" if "x\<in>A" for x
    using infsetsum_cong_neutral f0' B'B that
    by (metis (no_types, lifting) DiffD1 DiffD2 Int_iff inf.absorb_iff2 norm_zero)
  have "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A"
    using abs_summable_on_cong sum_A "*" by auto
  hence sum_A': "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A'"
    using _ A'A abs_summable_on_subset by blast 
  from sum_A' sum_B'
  have "f abs_summable_on Sigma A' B'"
    using abs_summable_on_Sigma_iff[where A=A' and B=B' and f=f, OF cnt_A' cnt_B'] A'A by auto
  moreover have "f x = 0"
    if "x \<in> Sigma A B - Sigma A' B'" for x
    using that f0 f0' by force     
  ultimately show "f abs_summable_on Sigma A B"
    by (rule abs_summable_on_zero_diff)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'c :: {banach, real_normed_field, second_countable_topology}"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  shows   abs_summable_on_product: "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    and   infsetsum_product: "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) =
                                infsetsum f A * infsetsum g B"
proof -
  from assms show "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    by (subst abs_summable_on_Sigma_iff)
      (auto simp: norm_mult infsetsum_cmult_right)
  with assms show "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) = infsetsum f A * infsetsum g B"
    by (subst infsetsum_Sigma)
      (auto simp: infsetsum_cmult_left infsetsum_cmult_right)
qed

end
