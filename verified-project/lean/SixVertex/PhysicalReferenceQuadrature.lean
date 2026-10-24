import SixVertex.PhysicalReferenceQuantiles
import SixVertex.ReferenceQuadrature

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem referenceQuantileDiscrepancy_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (L : ℕ) (hL : 0 < L) (Y : Fin n → ℝ) (hY : StrictMono Y)
    (hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ))
    (hlevels : ∀ j, (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2)
    (u : ℝ) (hu : u ∈ Icc (-Q) Q) :
    |referenceQuantileDiscrepancy lam h0 hpi Q L Y u| ≤ 1/2 := by
  let P : ℝ → ℝ := fun v => (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q v
  let xi : ℝ → ℝ := fun v => P v-(n : ℝ)/2
  have hLp : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hc := (finiteIntervalCumulative_strictMono_all lam h0 hpi Q).monotone
  have hpmono : Monotone P := fun x y hxy => mul_le_mul_of_nonneg_left (hc hxy) hLp
  have hximono : Monotone xi := fun x y hxy => sub_le_sub_right (hpmono hxy) _
  have hp0 : P (-Q)=0 := by dsimp [P]; rw [finiteIntervalCumulative_left,mul_zero]
  have hpn : P Q=(n : ℝ) := by dsimp [P]; rw [finiteIntervalCumulative_right lam h0 hpi Q hQ]; exact hmass
  have hlo : 0 ≤ P u := by have h := hpmono hu.1; rwa [hp0] at h
  have hhi : P u ≤ (n : ℝ) := by have h := hpmono hu.2; rwa [hpn] at h
  have hl : ∀ j : Fin n, xi (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2 := by
    intro j
    dsimp [xi,P]
    rw [hlevels j]
  have hh := ordered_count_sawtooth_local Y hY.monotone xi hximono hl u
    (by dsimp [xi]; linarith) (by dsimp [xi]; linarith)
  dsimp [xi] at hh
  change |(rootCountLe Y u : ℝ)-P u| ≤ 1/2
  simpa only [sub_add_cancel] using hh


/-- Uniform unweighted reference quadrature against a C1 test. Its
error is controlled by the L1 derivative alone, independently of Q,L. -/
theorem referenceQuantile_test_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (L : ℕ) (hL : 0 < L) (Y : Fin n → ℝ) (hY : StrictMono Y)
    (hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ))
    (hyloc : ∀ j, Y j ∈ Ioo (-Q) Q)
    (hlevels : ∀ j, (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2)
    (f f' : BoundedRealFunction) (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x)
    (hf' : Integrable (fun x => f' x)) :
    |(∑ j : Fin n, f (Y j))-(L : ℝ)*(∫ x in Icc (-Q) Q, f x*finiteIntervalDensity lam h0 hpi Q x)| ≤
      kernelL1Mass (fun x => f' x)/2 := by
  let P : ℝ → ℝ := fun x => (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q x
  let p : ℝ → ℝ := fun x => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q x
  have hPa : P (-Q)=0 := by dsimp [P]; rw [finiteIntervalCumulative_left,mul_zero]
  have hPb : P Q=(n : ℝ) := by dsimp [P]; rw [finiteIntervalCumulative_right lam h0 hpi Q hQ]; exact hmass
  have hdP (x : ℝ) : HasDerivAt P (p x) x := (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q x).const_mul (L : ℝ)
  have hF (x : ℝ) (hx : x ∈ Icc (-Q) Q) : |(rootCountLe Y x : ℝ)-P x| ≤ 1/2 :=
    referenceQuantileDiscrepancy_bound_all lam h0 hpi Q hQ L hL Y hY hmass hlevels x hx
  have he := finite_counting_quadrature_error Y f f' hd hf' P p
    (continuous_const.mul (finiteIntervalCumulative_continuous lam h0 hpi Q))
    (continuous_const.mul (finiteIntervalDensity lam h0 hpi Q).continuous) hdP
    (-Q) Q (by linarith) (fun j => ⟨(hyloc j).1.le,(hyloc j).2.le⟩) hPa hPb hF
  have hprod : (fun x => f x*p x)=fun x => (L : ℝ)*(f x*finiteIntervalDensity lam h0 hpi Q x) := by
    funext x
    dsimp [p]
    ring
  rw [hprod,integral_const_mul] at he
  exact he

/-- Kernel error for actual reference quantiles, including bounded phases
with nonzero end limits. Only the kernel derivative must be L1. -/
theorem referenceQuantile_kernel_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (L : ℕ) (hL : 0 < L) (Y : Fin n → ℝ) (hY : StrictMono Y)
    (hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ))
    (hyloc : ∀ j, Y j ∈ Ioo (-Q) Q)
    (hlevels : ∀ j, (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2)
    (q q' : BoundedRealFunction) (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x)
    (hq' : Integrable (fun x => q' x)) (u : ℝ) :
    |(∑ j : Fin n, q (u-Y j))-(L : ℝ)*(∫ x in Icc (-Q) Q, q (u-x)*finiteIntervalDensity lam h0 hpi Q x)| ≤
      kernelL1Mass (fun x => q' x)/2 := by
  let shift : ContinuousMap ℝ ℝ := ⟨fun v : ℝ => u-v,continuous_const.sub continuous_id⟩
  let f := q.compContinuous shift
  let f' := -(q'.compContinuous shift)
  have hdf (x : ℝ) : HasDerivAt (fun y => f y) (f' x) x := by
    simpa only [Function.comp_def,zero_sub,mul_neg_one] using!
      (hdq (u-x)).comp x ((hasDerivAt_const x u).sub (hasDerivAt_id x))
  have hi : Integrable (fun x => f' x) := (hq'.comp_sub_left u).neg
  have hm : kernelL1Mass (fun x => f' x)=kernelL1Mass (fun x => q' x) := by
    unfold kernelL1Mass
    change (∫ v : ℝ, |-(q' (u-v))|)=∫ v : ℝ, |q' v|
    simp only [abs_neg]
    exact integral_sub_left_eq_self (fun x : ℝ => |q' x|) volume u
  have he := referenceQuantile_test_error_all lam h0 hpi Q hQ L hL Y hY hmass hyloc hlevels f f' hdf hi
  rw [hm] at he
  exact he

end
end SixVertex
