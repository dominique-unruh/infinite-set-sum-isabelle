section \<open>Comparing the definitions\<close>
\<^latex>\<open>\label{section:Infsetsum_Infsum}\<close>

text \<open>This theory establishes the relationship between \<open>infsetsum\<close>
  (from the Isabelle/HOL standard library) and \<open>infsum\<close> (from the present development).
  In a nutshell: whenever \<open>infsetsum\<close> is defined, so is \<open>infsum\<close> and both have the same value.
  (The converse does not hold, even on types where \<open>infsetsum\<close> can be applied.)\<close>

theory Infsetsum_Infsum
  imports Infsetsum "HOL-Analysis.Infinite_Sum"
begin

no_notation Infinite_Sum.abs_summable_on (infixr "abs'_summable'_on" 46)


(* lemma abs_summable_summable_on: \<^latex>\<open>\label{lemma:abs_summable_summable_on}\<close>
  fixes f :: "'a\<Rightarrow>'b::{second_countable_topology,banach}" and A :: "'a set"
  assumes "f abs_summable_on A"
  shows "f summable_on A"
  by (simp add: assms infsum_abs_convergent_exists norm_summable_on_iff_abs_summable_on) *)


end
