import SixVertex.BoundedConvolution

namespace SixVertex
noncomputable section

theorem finite_operator_neumann_left {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hA : ‖A‖ < 1) :
    (∑' m : ℕ, (-A)^m)*(1+A)=1 := by
  have hn : ‖-A‖ < 1 := (norm_neg A).trans_lt hA
  exact (congrArg (fun T => (∑' m : ℕ, (-A)^m)*T) (sub_neg_eq_add (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) A)).symm.trans (geom_series_mul_neg (-A) hn)

theorem finite_operator_neumann_right {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hA : ‖A‖ < 1) :
    (1+A)*(∑' m : ℕ, (-A)^m)=1 := by
  have hn : ‖-A‖ < 1 := (norm_neg A).trans_lt hA
  exact (congrArg (fun T => T*(∑' m : ℕ, (-A)^m)) (sub_neg_eq_add (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) A)).symm.trans (mul_neg_geom_series (-A) hn)

theorem finite_operator_neumann_norm_bound {n : ℕ} (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (hA : ‖A‖ < 1) :
    ‖∑' m : ℕ, (-A)^m‖ ≤ (1-‖A‖)⁻¹ := by
  have hn : ‖-A‖ < 1 := (norm_neg A).trans_lt hA
  have h := tsum_geometric_le_of_norm_lt_one (-A) hn
  have hn1 : ‖(1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnA := norm_neg A
  rw [hnA] at h
  linarith


end
end SixVertex
