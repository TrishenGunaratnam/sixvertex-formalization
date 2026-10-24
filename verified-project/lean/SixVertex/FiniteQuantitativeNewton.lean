import SixVertex.PhysicalReferenceGaudin
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

namespace SixVertex
noncomputable section
open Set Metric
open scoped NNReal

/-- A finite-dimensional quantitative local-surjectivity criterion.
The derivative error and residual are genuine hypotheses; the six-vertex
application must establish both for its actual counting system. -/
theorem finite_quantitative_newton_exists_zero {n : ℕ}
    (f : (Fin n → ℝ) → (Fin n → ℝ))
    (df : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))
    (J B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (C radius : ℝ) (hC : 0 < C) (hrad : 0 ≤ radius)
    (hright : J*B=1) (hB : ‖B‖ ≤ C)
    (hderiv : ∀ v ∈ closedBall (0 : Fin n → ℝ) radius,HasFDerivAt f (df v) v)
    (herror : ∀ v ∈ closedBall (0 : Fin n → ℝ) radius,‖df v-J‖ ≤ 1/(2*C))
    (hres : ‖f 0‖ ≤ radius/(2*C)) :
    ∃ v : Fin n → ℝ,‖v‖ ≤ radius ∧ f v=0 := by
  let eps : ℝ≥0 := ⟨1/(2*C),by positivity⟩
  have heps : (eps : ℝ)=1/(2*C) := rfl
  have happ : ApproximatesLinearOn f J (closedBall (0 : Fin n → ℝ) radius) eps := by
    intro x hx y hy
    have hg (v : Fin n → ℝ) (hv : v ∈ closedBall (0 : Fin n → ℝ) radius) :
        HasFDerivWithinAt (fun w => f w-J w) (df v-J) (closedBall (0 : Fin n → ℝ) radius) v :=
      ((hderiv v hv).sub J.hasFDerivAt).hasFDerivWithinAt
    have ht := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg herror
      (convex_closedBall (0 : Fin n → ℝ) radius) hy hx
    have hid : f x-J x-(f y-J y)=f x-f y-J (x-y) := by rw [map_sub]; abel
    rw [hid] at ht
    exact ht
  let invJ : J.NonlinearRightInverse := {
    toFun := B
    nnnorm := ⟨C,hC.le⟩
    bound' := fun y => (B.le_opNorm y).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg y))
    right_inv' := fun y => by
      have h := congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T y) hright
      simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using h }
  have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse invJ hrad (Subset.refl _)
  have hrad_eq : ((invJ.nnnorm : ℝ)⁻¹-(eps : ℝ))*radius=radius/(2*C) := by
    change (C⁻¹-1/(2*C))*radius=radius/(2*C)
    field_simp
    <;> ring
  have hmem : (0 : Fin n → ℝ) ∈ closedBall (f 0) (((invJ.nnnorm : ℝ)⁻¹-eps)*radius) := by
    rw [mem_closedBall,dist_zero_left,hrad_eq]
    exact hres
  obtain ⟨v,hv,hzero⟩ := hsurj hmem
  exact ⟨v,by simpa only [mem_closedBall,dist_zero_right] using hv,hzero⟩

end
end SixVertex
