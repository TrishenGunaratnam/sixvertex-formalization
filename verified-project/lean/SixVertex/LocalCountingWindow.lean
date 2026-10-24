import SixVertex.CountingPrimitive
import SixVertex.CountingDiscrepancyKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Only the counting window at the test point is needed. This permits
sub-half-filled root lists without asserting a global sawtooth bound. -/
theorem ordered_count_sawtooth_local {n : ℕ} (Y : Fin n → ℝ) (hY : Monotone Y)
    (xi : ℝ → ℝ) (hxi : Monotone xi)
    (hlevels : ∀ j : Fin n, xi (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2)
    (u : ℝ) (hlo : -(n : ℝ)/2 ≤ xi u) (hhi : xi u ≤ (n : ℝ)/2) :
    |(rootCountLe Y u : ℝ)-(xi u+(n : ℝ)/2)| ≤ 1/2 := by
  let m:=rootCountLe Y u
  have hmn : m ≤ n := rootCountLe_le Y u
  apply abs_le.mpr
  constructor
  · by_cases hm : m < n
    · let j : Fin n := ⟨m,hm⟩
      have hy : u < Y j := by
        by_contra hn
        have hh:=rootCountLe_ge_index Y hY u j (le_of_not_gt hn)
        change m+1 ≤ m at hh
        omega
      have hh:xi u ≤ (m : ℝ)+1/2-(n : ℝ)/2 := by
        simpa only [j] using (hxi hy.le).trans_eq (hlevels j)
      change -(1/2 : ℝ) ≤ (m : ℝ)-(xi u+(n : ℝ)/2)
      linarith
    · have hm':m=n:=by omega
      change -(1/2 : ℝ) ≤ (m : ℝ)-(xi u+(n : ℝ)/2)
      rw [hm']
      linarith [hhi]
  · by_cases hm : m=0
    · change (m : ℝ)-(xi u+(n : ℝ)/2) ≤ 1/2
      rw [hm]
      simp only [Nat.cast_zero]
      linarith [hlo]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let j : Fin n := ⟨m-1,by omega⟩
      have hy : Y j ≤ u := by
        by_contra hn
        have hh:=rootCountLe_le_index Y hY u j (lt_of_not_ge hn)
        change m ≤ m-1 at hh
        omega
      have hh:= (hlevels j).symm.trans_le (hxi hy)
      change ((m-1 : ℕ) : ℝ)+1/2-(n : ℝ)/2 ≤ xi u at hh
      rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one] at hh
      change (m : ℝ)-(xi u+(n : ℝ)/2) ≤ 1/2
      linarith


theorem countingDiscrepancy_bound_in_window {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0) (u : ℝ)
    (hlo : -(n : ℝ)/2 ≤ countingXi lam b L Y u)
    (hhi : countingXi lam b L Y u ≤ (n : ℝ)/2) :
    |countingDiscrepancy lam b L Y u| ≤ 1/2 := by
  apply ordered_count_sawtooth_local Y hroots.1.monotone (countingXi lam b L Y)
    (countingXi_strictMono_nonpositiveK lam b L hL Y hhalf hpi).monotone
    _ u hlo hhi
  intro j
  calc
    _ = countingTarget n 0 j := congrFun hroots.2 j
    _ = _ := by unfold countingTarget; ring

/-- The bounded primitive exists at every filling. The constant corrects
the end mass rather than silently imposing the half-filled relation. -/
def generalCountingPrimitiveFunction {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : BoundedRealFunction :=
  sourcePrimitiveFunction lam b L - atomicPrimitiveFunction lam Y +
    BoundedContinuousFunction.const ℝ ((n : ℝ)/2-countingEnd lam L n)

theorem generalCountingPrimitiveFunction_apply {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) :
    generalCountingPrimitiveFunction lam b L Y u=countingXi lam b L Y u+(n : ℝ)/2 := by
  change sourcePrimitiveFunction lam b L u-atomicPrimitiveFunction lam Y u+
    ((n : ℝ)/2-countingEnd lam L n)=_
  rw [sourcePrimitiveFunction_apply,atomicPrimitiveFunction_apply]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,countingXi,countingEnd]
  ring

theorem generalCountingPrimitiveFunction_hasDerivAt {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u : ℝ) :
    HasDerivAt (fun v => generalCountingPrimitiveFunction lam b L Y v)
      (countingSlope lam b L Y u) u := by
  simp_rw [generalCountingPrimitiveFunction_apply]
  exact (hasDerivAt_countingXi lam b L Y u h0 hpi).add_const ((n : ℝ)/2)

/-- The exact discrete/smooth identity holds at every filling. A local
counting-window condition is used only for its quantitative error bound. -/
theorem countingDiscrepancy_kernel_identity_general {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (q q' : BoundedRealFunction) (hq : Integrable (fun x => q x)) (hq' : Integrable (fun x => q' x))
    (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x) (u : ℝ) :
    (∫ v : ℝ, q' (u-v)*countingDiscrepancy lam b L Y v)=
      (∑ j : Fin n, q (u-Y j))-(∫ v : ℝ, q (u-v)*countingSlope lam b L Y v) := by
  let P := generalCountingPrimitiveFunction lam b L Y
  have hp := countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi
  have hdP := generalCountingPrimitiveFunction_hasDerivAt lam b L Y
    (by linarith [Real.pi_pos]) hpi
  have hc := bounded_measurable_convolution_integrable (fun v => q' v)
    (fun v => (rootCountLe Y v : ℝ)) hq' (rootCountLe_measurable Y).aestronglyMeasurable (n : ℝ)
    (rootCountLe_norm_bound Y) u
  have hP := bounded_measurable_convolution_integrable (fun v => q' v)
    (fun v => P v) hq' P.continuous.aestronglyMeasurable ‖P‖ P.norm_coe_le_norm u
  have he : countingDiscrepancy lam b L Y=fun v => (rootCountLe Y v : ℝ)-P v := by
    funext v
    rw [show P v=countingXi lam b L Y v+(n : ℝ)/2 from
      generalCountingPrimitiveFunction_apply lam b L Y v]
    rfl
  rw [he]
  simp_rw [mul_sub]
  rw [integral_sub hc hP,integral_derivative_kernel_rootCount Y q q' hq hq' hdq,
    ← convolution_primitive_integration_by_parts q q' P hq hq' _ hp hdq hdP u]

end
end SixVertex
