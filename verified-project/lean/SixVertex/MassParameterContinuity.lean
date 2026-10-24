import SixVertex.InverseParameterContinuity
import SixVertex.FiniteIntervalMassStrict

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem finiteIntervalDensity_uniform_norm (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    ‖finiteIntervalDensity lam h0 hpi Q‖ ≤
      (1-|1-2*lam/Real.pi|)⁻¹*‖physicalSourceFunction lam h0 hpi‖ :=
  (ContinuousLinearMap.le_opNorm (physicalWindowInverse lam h0 hpi Q) (physicalSourceFunction lam h0 hpi)).trans
    (mul_le_mul_of_nonneg_right (physicalWindowInverse_norm_bound lam h0 hpi Q) (norm_nonneg _))

/-- The actual filling mass is Lipschitz on each bounded interval of
nonnegative cutoffs, for every physical lambda. -/
theorem exists_finiteIntervalMass_lipschitz_on (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q T : ℝ), Q ∈ Icc 0 A → T ∈ Icc 0 A →
      |finiteIntervalMass lam h0 hpi Q-finiteIntervalMass lam h0 hpi T| ≤ C*|Q-T| := by
  obtain ⟨d,hd,hD⟩ := exists_finiteIntervalDensity_lipschitz_Q lam h0 hpi
  let b : ℝ := (1-|1-2*lam/Real.pi|)⁻¹*‖physicalSourceFunction lam h0 hpi‖
  have hb (T : ℝ) : ‖finiteIntervalDensity lam h0 hpi T‖ ≤ b := finiteIntervalDensity_uniform_norm lam h0 hpi T
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  let C : ℝ := 2*A*d+2*b
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro Q T hQ hT
  let q := finiteIntervalDensity lam h0 hpi Q
  let t := finiteIntervalDensity lam h0 hpi T
  have hfixed : ‖∫ u in Icc (-Q) Q, q u-t u‖ ≤ (2*A*d)*|Q-T| := by
    have hs := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-Q) Q)
      (f := fun u => q u-t u) (C := ‖q-t‖) isCompact_Icc.measure_lt_top
      (fun u _ => (q-t).norm_coe_le_norm u)
    rw [Real.volume_real_Icc_of_le (by linarith [hQ.1])] at hs
    calc
      _ ≤ ‖q-t‖*(2*Q) := by convert hs using 1 <;> ring
      _ ≤ (d*|Q-T|)*(2*Q) := mul_le_mul_of_nonneg_right (hD Q T hQ.1 hT.1) (by linarith [hQ.1])
      _ ≤ (d*|Q-T|)*(2*A) := mul_le_mul_of_nonneg_left (by linarith [hQ.2]) (by positivity)
      _ = _ := by ring
  have hmoving : ‖(∫ u in Icc (-Q) Q, t u)-(∫ u in Icc (-T) T, t u)‖ ≤ 2*b*|Q-T| :=
    symmetric_interval_integral_norm_sub_le _ t.continuous b
      (fun u => (t.norm_coe_le_norm u).trans (hb T)) Q T hQ.1 hT.1
  have he : finiteIntervalMass lam h0 hpi Q-finiteIntervalMass lam h0 hpi T=
      (∫ u in Icc (-Q) Q, q u-t u)+
      ((∫ u in Icc (-Q) Q, t u)-(∫ u in Icc (-T) T, t u)) := by
    rw [integral_sub (finiteIntervalDensity_integrable lam h0 hpi Q).integrableOn
      (finiteIntervalDensity_integrable lam h0 hpi T).integrableOn]
    dsimp [finiteIntervalMass,q,t]
    ring
  change ‖finiteIntervalMass lam h0 hpi Q-finiteIntervalMass lam h0 hpi T‖ ≤ C*|Q-T|
  rw [he]
  calc
    _ ≤ ‖∫ u in Icc (-Q) Q, q u-t u‖+
      ‖(∫ u in Icc (-Q) Q, t u)-(∫ u in Icc (-T) T, t u)‖ := norm_add_le _ _
    _ ≤ (2*A*d)*|Q-T|+2*b*|Q-T| := add_le_add hfixed hmoving
    _ = _ := by dsimp [C]; ring

end
end SixVertex

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem continuousOn_finiteIntervalMass_Icc (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (A : ℝ) (hA : 0 ≤ A) : ContinuousOn (finiteIntervalMass lam h0 hpi) (Icc 0 A) := by
  obtain ⟨C,hC,hbound⟩ := exists_finiteIntervalMass_lipschitz_on lam h0 hpi A hA
  have hlip : LipschitzOnWith ⟨C,hC⟩ (finiteIntervalMass lam h0 hpi) (Icc 0 A) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro Q hQ T hT
    change |finiteIntervalMass lam h0 hpi Q-finiteIntervalMass lam h0 hpi T| ≤ C*|Q-T|
    exact hbound Q T hQ hT
  exact hlip.continuousOn

/-- An actual positive cutoff exists for every sub-half filling, in the
negative-kernel regime, by the proved mass limit and continuity. -/
theorem exists_finiteIntervalCutoff (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (rho : ℝ)
    (hrho : 0 < rho) (hrhohalf : rho < 1/2) :
    ∃ Q : ℝ, 0 < Q ∧ finiteIntervalMass lam h0 hpi Q=rho := by
  have he := (finiteIntervalMass_tendsto_half lam h0 hhalf hpi).eventually (Ioi_mem_nhds hrhohalf)
  obtain ⟨A,hA,hfillA⟩ := ((eventually_ge_atTop (1 : ℝ)).and he).exists
  have hA0 : 0 ≤ A := by linarith
  have hin : rho ∈ Icc (finiteIntervalMass lam h0 hpi 0) (finiteIntervalMass lam h0 hpi A) := by
    rw [finiteIntervalMass_zero]
    exact ⟨hrho.le,le_of_lt hfillA⟩
  obtain ⟨Q,hQI,hQeq⟩ := intermediate_value_Icc hA0 (continuousOn_finiteIntervalMass_Icc lam h0 hpi A hA0) hin
  refine ⟨Q,?_,hQeq⟩
  by_contra hn
  have hQzero : Q=0 := le_antisymm (le_of_not_gt hn) hQI.1
  rw [hQzero,finiteIntervalMass_zero] at hQeq
  linarith

end
end SixVertex
