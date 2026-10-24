import SixVertex.PhysicalRootCountingData
import SixVertex.RootIntervalCount

namespace SixVertex
noncomputable section
open Set

/-- Actual inverse-reference-density atoms have uniformly bounded mass
on every fixed-length interval, for both physical kernel signs. The
bound remains uniform as the interval moves towards a sparse edge. -/
theorem reference_weighted_interval_mass_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (a z : ℝ) (haz : a ≤ z) :
    (∑ j ∈ rootsInInterval Y a z,((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹) ≤
      (Real.exp (physicalDensityLogConstant lam*(z-a)))^2*(z-a)+
        Real.exp (physicalDensityLogConstant lam*(z-a))/M := by
  classical
  let s := rootsInInterval Y a z
  let len := z-a
  let E := Real.exp (physicalDensityLogConstant lam*len)
  let w : ℝ → ℝ := fun u => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u
  let P : ℝ → ℝ := fun u => (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u
  have hlen : 0 ≤ len := sub_nonneg.mpr haz
  have hE : 0 < E := Real.exp_pos _
  have hwp (u : ℝ) : 0 < w u := mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos_all lam h0 hpi Q u)
  have hcomp (u v : ℝ) : w v ≤ Real.exp (physicalDensityLogConstant lam*|v-u|)*w u := by
    exact (mul_le_mul_of_nonneg_left (finiteIntervalDensity_exponential_comparison_all lam h0 hpi Q u v).2
      (Nat.cast_nonneg L : (0 : ℝ) ≤ L)).trans_eq (by dsimp [w]; ring)
  change (∑ j ∈ s,(w (Y j))⁻¹) ≤ E^2*len+E/M
  by_cases hs : s.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hs
    have hy₀ : Y j₀ ∈ Icc a z := (Finset.mem_filter.mp hj₀).2
    let p := w (Y j₀)
    have hp : 0 < p := hwp _
    have hself : M ≤ p := hlower (Y j₀) ⟨(R.location j₀).1.le,(R.location j₀).2.le⟩
    have hdist (v : ℝ) (hv : v ∈ Icc a z) : |v-Y j₀| ≤ len := by
      apply abs_le.mpr
      dsimp [len]
      constructor <;> linarith [hv.1,hv.2,hy₀.1,hy₀.2]
    have hup (v : ℝ) (hv : v ∈ Icc a z) : w v ≤ E*p :=
      (hcomp (Y j₀) v).trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdist v hv) (physicalDensityLogConstant_pos lam h0).le)) hp.le)
    have hweight (j : Fin n) (hj : j ∈ s) : (w (Y j))⁻¹ ≤ E/p := by
      have hv : Y j ∈ Icc a z := (Finset.mem_filter.mp hj).2
      have hh := hcomp (Y j) (Y j₀)
      have he : Real.exp (physicalDensityLogConstant lam*|Y j₀-Y j|) ≤ E := by
        rw [abs_sub_comm]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdist (Y j) hv) (physicalDensityLogConstant_pos lam h0).le)
      have hpq : p ≤ E*w (Y j) := hh.trans (mul_le_mul_of_nonneg_right he (hwp _).le)
      apply (le_div_iff₀ hp).mpr
      have hd := (div_le_iff₀ (hwp _)).mpr hpq
      simpa only [div_eq_mul_inv,mul_comm] using hd
    have hxi := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v (_ : v ∈ Icc a z) => ((finiteIntervalCumulative_hasDerivAt lam h0 hpi Q v).const_mul (L : ℝ)).hasDerivWithinAt)
      (fun v (hv : v ∈ Icc a z) => by rw [Real.norm_of_nonneg (hwp v).le]; exact hup v hv)
      (convex_Icc a z) (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz)
    have hdiff : P z-P a ≤ E*p*len := by
      have hh := (le_abs_self (P z-P a)).trans hxi
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr haz)] using hh
    have hmono : Monotone P := fun u v huv => mul_le_mul_of_nonneg_left
      ((finiteIntervalCumulative_strictMono_all lam h0 hpi Q).monotone huv) (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    have hcount : (s.card : ℝ) ≤ E*p*len+1 :=
      (consecutive_levels_interval_count Y P hmono (1/2) R.level a z haz).trans (add_le_add hdiff le_rfl)
    calc
      _ ≤ ∑ _j ∈ s,E/p := Finset.sum_le_sum hweight
      _ = (s.card : ℝ)*(E/p) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (E*p*len+1)*(E/p) := mul_le_mul_of_nonneg_right hcount (div_nonneg hE.le hp.le)
      _ = E^2*len+E/p := by field_simp [hp.ne']
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left hE.le hM hself)
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [he,Finset.sum_empty]
    positivity

end
end SixVertex
