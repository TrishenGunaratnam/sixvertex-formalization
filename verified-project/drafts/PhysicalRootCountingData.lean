import SixVertex.PhysicalCountingPhase

namespace SixVertex
noncomputable section
open Set

/-- One uniform construction supplies the actual ordered roots,both
whole-line counting errors and the actual nonsingular Gaudin matrix.
In particular its primitive estimate controls both continuum endpoints. -/
theorem exists_weighted_reference_root_counting_data_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ M₀ radius C : ℝ,0 < M₀ ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C) ∧
        (∀ u : ℝ,|countingXi lam (fun _ => 0) L X u-
          ((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 := by
  obtain ⟨M,radius,D,hM,hrad,hD,hroots⟩ := exists_weighted_reference_regular_roots_all lam h0 hpi
  let E := Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+|1-2*lam/Real.pi|/2
  have hE : 0 ≤ E := by
    dsimp [E]
    exact add_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hrad.le)
      (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)))
      (div_nonneg (abs_nonneg _) (by norm_num))
  refine ⟨M,radius,D+E+1,hM,hrad,by linarith,?_⟩
  intro n Q L Y R hlower
  obtain ⟨X,hX,hclose,hdens,hdet⟩ := hroots n Q L Y R hlower
  refine ⟨X,hX,hclose,?_,?_,hdet⟩
  · intro u
    exact (hdens u).trans (by linarith)
  · intro u
    exact (weighted_configuration_counting_primitive_error_all lam h0 hpi Q L Y X R M radius hM hrad.le hlower hclose u).trans
      (by change E ≤ D+E+1; linarith)

end
end SixVertex
