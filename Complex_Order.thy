theory Complex_Order
  imports Complex_Main
begin

instantiation complex :: order begin

definition \<open>x < y \<longleftrightarrow> Re x < Re y \<and> Im x = Im y\<close>
definition \<open>x \<le> y \<longleftrightarrow> Re x \<le> Re y \<and> Im x = Im y\<close>

instance
  apply standard
  by (auto simp: less_complex_def less_eq_complex_def complex_eq_iff)
end

instance complex :: ordered_comm_ring
  apply standard
  by (auto simp: less_complex_def less_eq_complex_def complex_eq_iff mult_left_mono mult_right_mono)

instance complex :: ordered_real_vector
  apply standard
  by (auto simp: less_complex_def less_eq_complex_def mult_left_mono mult_right_mono)

instance complex :: ordered_cancel_comm_semiring
  by standard

end
