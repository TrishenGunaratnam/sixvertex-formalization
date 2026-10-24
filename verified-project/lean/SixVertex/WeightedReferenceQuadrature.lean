import SixVertex.FiniteIntervalRegularity
import SixVertex.ReferenceQuantileGeometry
import SixVertex.FiniteQuadratureError
import SixVertex.NormalizedTest

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def weightedReferenceTest (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (q : BoundedRealFunction) (u v : ℝ) : ℝ :=
  q (u-v)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)

def weightedReferenceTestPrime (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (q q' : BoundedRealFunction) (u v : ℝ) : ℝ :=
  ((-q' (u-v))*((L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)-
    q (u-v)*((L : ℝ)*finiteIntervalDensityPrimeFunction lam h0 hpi Q v))/
    ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)^2

theorem weightedReferenceTest_hasDerivAt (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (hL : 0 < L)
    (q q' : BoundedRealFunction) (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x) (u v : ℝ) :
    HasDerivAt (weightedReferenceTest lam h0 hpi Q L q u)
      (weightedReferenceTestPrime lam h0 hpi Q L q q' u v) v := by
  have hd : HasDerivAt (fun x => q (u-x)) (-q' (u-v)) v := by
    simpa only [Function.comp_def,zero_sub,mul_neg_one] using!
      (hdq (u-v)).comp v ((hasDerivAt_const v u).sub (hasDerivAt_id v))
  exact hd.div ((finiteIntervalDensity_hasDerivAt lam h0 hpi Q v).const_mul (L : ℝ))
    (mul_pos (Nat.cast_pos.mpr hL) (finiteIntervalDensity_pos lam h0 hhalf hpi Q v)).ne'

theorem weightedReferenceTestPrime_continuous (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (hL : 0 < L)
    (q q' : BoundedRealFunction) (u : ℝ) :
    Continuous (weightedReferenceTestPrime lam h0 hpi Q L q q' u) := by
  apply Continuous.div
  · exact (((q'.continuous.comp (continuous_const.sub continuous_id)).neg.mul
        (continuous_const.mul (finiteIntervalDensity lam h0 hpi Q).continuous)).sub
      ((q.continuous.comp (continuous_const.sub continuous_id)).mul
        (continuous_const.mul (finiteIntervalDensityPrimeFunction lam h0 hpi Q).continuous)))
  · exact (continuous_const.mul (finiteIntervalDensity lam h0 hpi Q).continuous).pow 2
  · intro v
    exact pow_ne_zero 2 (mul_pos (Nat.cast_pos.mpr hL) (finiteIntervalDensity_pos lam h0 hhalf hpi Q v)).ne'

/-- The actual quotient derivative has a local L1 majorant of size1/M. -/
theorem weightedReferenceTestPrime_bound (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (hL : 0 < L)
    (q q' : BoundedRealFunction) (u v M : ℝ) (hM : 0 < M)
    (hlower : M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) :
    |weightedReferenceTestPrime lam h0 hpi Q L q q' u v| ≤
      (|q' (u-v)|+kernelLogConstant lam*|q (u-v)|)/M := by
  have hLp : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hrel : |(L : ℝ)*finiteIntervalDensityPrimeFunction lam h0 hpi Q v| ≤
      kernelLogConstant lam*((L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) := by
    rw [abs_mul,abs_of_nonneg hLp]
    apply (mul_le_mul_of_nonneg_left (finiteIntervalDensityPrime_relative_bound lam h0 hhalf hpi Q v) hLp).trans_eq
    ring
  simpa only [weightedReferenceTestPrime, abs_neg] using normalized_derivative_scalar_bound (q (u-v)) (-q' (u-v))
    ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) ((L : ℝ)*finiteIntervalDensityPrimeFunction lam h0 hpi Q v)
    M (kernelLogConstant lam) hM hlower (kernelLogConstant_nonneg lam) hrel

/-- Actual weighted reference quadrature, including the density derivative
term. No weighted-row estimate is supplied as a hypothesis. -/
theorem weighted_reference_kernel_error {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (q q' : BoundedRealFunction) (hq : Integrable (fun x => q x)) (hq' : Integrable (fun x => q' x))
    (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x) (u : ℝ) :
    |(∑ j : Fin n, q (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))-
      (∫ v in Icc (-Q) Q, q (u-v))| ≤
      (kernelL1Mass (fun x => q' x)+kernelLogConstant lam*kernelL1Mass (fun x => q x))/(2*M) := by
  let f := weightedReferenceTest lam h0 hpi Q L q u
  let f' := weightedReferenceTestPrime lam h0 hpi Q L q q' u
  let P : ℝ → ℝ := fun v => (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q v
  let p : ℝ → ℝ := fun v => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v
  have hPa : P (-Q)=0 := by dsimp [P]; rw [finiteIntervalCumulative_left,mul_zero]
  have hPb : P Q=(n : ℝ) := by dsimp [P]; rw [finiteIntervalCumulative_right lam h0 hpi Q R.interval_nonneg]; exact R.mass
  have he := finite_counting_local_quadrature_error Y f f'
    (weightedReferenceTestPrime_continuous lam h0 hhalf hpi Q L R.chain_pos q q' u)
    (weightedReferenceTest_hasDerivAt lam h0 hhalf hpi Q L R.chain_pos q q' hdq u)
    P p (continuous_const.mul (finiteIntervalCumulative_continuous lam h0 hpi Q))
    (continuous_const.mul (finiteIntervalDensity lam h0 hpi Q).continuous)
    (fun v => (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q v).const_mul (L : ℝ))
    (-Q) Q (by linarith [R.interval_nonneg])
    (fun j => ⟨(R.location j).1.le,(R.location j).2.le⟩) hPa hPb
    (fun v hv => referenceQuantileDiscrepancy_bound lam h0 hhalf hpi Q R.interval_nonneg L R.chain_pos Y
      R.ordered R.mass R.level v hv)
  have hcancel (v : ℝ) : f v*p v=q (u-v) := by
    exact div_mul_cancel₀ _ (mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos lam h0 hhalf hpi Q v)).ne'
  simp_rw [hcancel] at he
  apply he.trans
  let G : ℝ → ℝ := fun v => (|q' (u-v)|+kernelLogConstant lam*|q (u-v)|)/M
  have hG : Integrable G :=
    (((hq'.abs.comp_sub_left u).add ((hq.abs.comp_sub_left u).const_mul (kernelLogConstant lam))).div_const M)
  have hbound : (∫ v in Icc (-Q) Q, |f' v|) ≤ ∫ v : ℝ, G v := by
    calc
      (∫ v in Icc (-Q) Q, |f' v|) ≤ ∫ v in Icc (-Q) Q, G v := by
        apply integral_mono_ae
          (weightedReferenceTestPrime_continuous lam h0 hhalf hpi Q L R.chain_pos q q' u).abs.integrableOn_Icc hG.integrableOn
        apply (ae_restrict_iff' measurableSet_Icc).mpr
        exact Eventually.of_forall (fun v hv => weightedReferenceTestPrime_bound lam h0 hhalf hpi Q L R.chain_pos q q' u v M hM (hlower v hv))
      _ ≤ ∫ v : ℝ, G v := by
        apply setIntegral_le_integral hG
        apply Eventually.of_forall
        intro v
        dsimp [G]
        have hC := kernelLogConstant_nonneg lam
        positivity
  have hIntG : (∫ v : ℝ, G v)=
      (kernelL1Mass (fun x => q' x)+kernelLogConstant lam*kernelL1Mass (fun x => q x))/M := by
    dsimp [G]
    rw [integral_div,integral_add (hq'.abs.comp_sub_left u)
      ((hq.abs.comp_sub_left u).const_mul (kernelLogConstant lam)),integral_const_mul,
      integral_sub_left_eq_self (fun x : ℝ => |q' x|) volume u,
      integral_sub_left_eq_self (fun x : ℝ => |q x|) volume u]
    rfl
  apply (div_le_div_of_nonneg_right hbound (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  rw [hIntG]
  ring

end
end SixVertex
