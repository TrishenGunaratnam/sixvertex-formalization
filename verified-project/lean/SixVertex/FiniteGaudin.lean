import SixVertex.FiniteBetheKernels
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace SixVertex

open scoped ContDiff

noncomputable def countingXi {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) : ℝ :=
  (∑ a ∈ Finset.range L, countingS lam (u-b a)) - ∑ k, countingTheta lam (u-Y k)

noncomputable def countingSlope {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) : ℝ :=
  (∑ a ∈ Finset.range L, kernelS lam (u-b a)) - ∑ k, kernelK lam (u-Y k)

noncomputable def countingSystem {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : Fin n → ℝ := fun j => countingXi lam b L Y (Y j)

noncomputable def countingTarget (n : ℕ) (twist : ℝ) : Fin n → ℝ :=
  fun j => (j.val : ℝ) + 1 - ((n : ℝ)+1)/2 + twist/Real.pi

def ConsecutiveRoots {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) : Prop :=
  StrictMono Y ∧ countingSystem lam b L Y = countingTarget n twist

noncomputable def gaudinMatrix {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun j k => (if j = k then countingSlope lam b L Y (Y j) else 0) +
    kernelK lam (Y j-Y k))

noncomputable def gaudinCLM {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (gaudinMatrix lam b L Y).toLin'.toContinuousLinearMap

theorem hasDerivAt_countingXi {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasDerivAt (countingXi lam b L Y) (countingSlope lam b L Y u) u := by
  unfold countingXi countingSlope
  apply HasDerivAt.sub
  · apply HasDerivAt.fun_sum
    intro a ha
    simpa only [Function.comp_def, id_eq, mul_one] using (hasDerivAt_countingS lam (u-b a) h0 hpi).comp u
      ((hasDerivAt_id u).sub_const (b a))
  · apply HasDerivAt.fun_sum
    intro k hk
    simpa only [Function.comp_def, id_eq, mul_one] using (hasDerivAt_countingTheta lam (u-Y k) h0 hpi).comp u
      ((hasDerivAt_id u).sub_const (Y k))

/-- Frechet derivative of the root-counting system, with the self term
cancelled by the moving evaluation coordinate. -/
theorem hasFDerivAt_countingSystem {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasFDerivAt (countingSystem lam b L) (gaudinCLM lam b L Y) Y := by
  classical
  have hs : ∀ j : Fin n, HasFDerivAt (fun X : Fin n → ℝ =>
      ∑ a ∈ Finset.range L, countingS lam (X j-b a))
      (∑ a ∈ Finset.range L, kernelS lam (Y j-b a) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) Y := by
    intro j
    apply HasFDerivAt.fun_sum
    intro a ha
    exact (hasDerivAt_countingS lam (Y j-b a) h0 hpi).comp_hasFDerivAt Y
      ((hasFDerivAt_apply j Y).sub_const (b a))
  have hk : ∀ j : Fin n, HasFDerivAt (fun X : Fin n → ℝ =>
      ∑ k, countingTheta lam (X j-X k))
      (∑ k, kernelK lam (Y j-Y k) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k)) Y := by
    intro j
    apply HasFDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_countingTheta lam (Y j-Y k) h0 hpi).comp_hasFDerivAt Y
      ((hasFDerivAt_apply j Y).sub (hasFDerivAt_apply k Y))
  apply hasFDerivAt_pi'.mpr
  intro j
  convert (hs j).sub (hk j) using 1
  · rfl
  · ext H
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, gaudinCLM,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      gaudinMatrix, Matrix.of_apply, countingSlope, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      mul_sub, Finset.sum_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring

/-- The counting map is real analytic, not merely continuously differentiable. -/
theorem contDiff_countingSystem {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) :
    ContDiff ℝ ω (countingSystem (n := n) lam b L) := by
  have heval (j : Fin n) : ContDiff ℝ ω (fun X : Fin n → ℝ => X j) := contDiff_apply ℝ (fun _ : Fin n => ℝ) j
  apply contDiff_pi.mpr
  intro j
  apply ContDiff.sub
  · apply ContDiff.sum
    intro a ha
    exact (contDiff_barePhase (lam/2)).comp ((heval j).sub contDiff_const)
  · apply ContDiff.sum
    intro k hk
    exact (contDiff_barePhase lam).comp ((heval j).sub (heval k))

/-- Matrix multiplication by the Gaudin weights, with exactly the column
weight convention K(j,k) * ell(k) from the manuscript. -/
theorem gaudin_weight_identity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hpos : ∀ j, 0 < countingSlope lam b L Y (Y j)) :
    gaudinMatrix lam b L Y * Matrix.diagonal (fun j => (countingSlope lam b L Y (Y j))⁻¹) =
      1 + Matrix.of (fun j k => kernelK lam (Y j-Y k) * (countingSlope lam b L Y (Y k))⁻¹) := by
  ext j k
  simp only [Matrix.mul_diagonal, gaudinMatrix, Matrix.of_apply, Matrix.add_apply,
    Matrix.one_apply]
  by_cases hjk : j = k
  · subst k
    simp [add_mul, (hpos j).ne']
  · simp [hjk]

end SixVertex
