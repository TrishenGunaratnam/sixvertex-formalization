import SixVertex.CountingTailDiscrepancy

namespace SixVertex
noncomputable section
open MeasureTheory Set

theorem dressedBareDensityFunction_apply_sum (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    dressedBareDensityFunction lam h0 hpi b L u=
      ∑ a ∈ Finset.range L, fullLineDensityFunction lam h0 hpi (u-b a) := by
  rw [dressedBareDensityFunction_eq_sum,BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rfl

/-- The complete first item of Lemma 3.1, with constants fixed before
all chain lengths and real site arrays. The density r uses its primary
inverse-operator definition from Section 2; its separate closed-form
hyperbolic evaluation is not asserted here. The other items and Perron
clauses of Lemma 3.1 remain separate. -/
theorem half_filled_roots_and_uniform_densities (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ C₀ C₁ : ℝ, ∀ (b : ℕ → ℝ) (L n : ℕ), 0 < L → L=2*n →
      ∃ Y : Fin n → ℝ, ConsecutiveRoots lam b L Y 0 ∧
        ∀ u : ℝ, 0 < countingSlope lam b L Y u ∧
          |countingSlope lam b L Y u-
            (∑ a ∈ Finset.range L, fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi (u-b a))| ≤ C₀ ∧
          |∫ v in Iic u, countingSlope lam b L Y v-
            (∑ a ∈ Finset.range L, fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi (v-b a))| ≤ C₁ := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  refine ⟨(1-kernelL1Mass (kernelK lam))⁻¹*(kernelL1Mass (kernelKPrime lam)/2),
    (1-kernelL1Mass (kernelK lam))⁻¹*(kernelL1Mass (kernelK lam)/2),?_⟩
  intro b L n hL hfill
  obtain ⟨Y,hroots,_⟩ := exists_unique_nonpositiveKernel_roots lam b L hL hhalf.le hpi n (by omega)
  refine ⟨Y,hroots,fun u => ⟨countingSlope_pos_nonpositiveK lam b L hL Y u hhalf.le hpi,
    half_filled_density_uniform_bound lam b L hL hfill Y hhalf.le hpi hroots u,?_⟩⟩
  have he : (fun v => countingSlope lam b L Y v-
      (∑ a ∈ Finset.range L, fullLineDensityFunction lam h0 hpi (v-b a)))=
      (fun v => countingSlope lam b L Y v-dressedBareDensityFunction lam h0 hpi b L v) := by
    funext v
    rw [dressedBareDensityFunction_apply_sum]
  rw [he]
  exact half_filled_integrated_density_uniform_bound lam b L hL hfill Y hhalf.le hpi hroots u

end
end SixVertex
