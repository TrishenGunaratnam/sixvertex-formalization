import SixVertex.PositiveNeumann
import SixVertex.FiniteIntervalSymmetry

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology

def RadiallyAntitone (f : ℝ → ℝ) : Prop := ∀ u v, |u| ≤ |v| → f v ≤ f u

theorem RadiallyAntitone.even {f : ℝ → ℝ} (hf : RadiallyAntitone f) (u : ℝ) : f (-u)=f u := by
  apply le_antisymm
  · exact hf u (-u) (by rw [abs_neg])
  · exact hf (-u) u (by rw [abs_neg])

theorem radiallyAntitone_of_even_positive_half (f : ℝ → ℝ) (heven : ∀ u, f (-u)=f u)
    (hmono : ∀ u v, 0 ≤ u → u ≤ v → f v ≤ f u) : RadiallyAntitone f := by
  have habs (u : ℝ) : f |u|=f u := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu),heven]
  intro u v huv
  simpa only [habs] using hmono |u| |v| (abs_nonneg u) huv

/-- Pairing integration variables about (x+y)/2 makes the radial
convolution inequality pointwise nonnegative. -/
theorem radial_convolution_pair_nonneg (k f : ℝ → ℝ)
    (hk : RadiallyAntitone k) (hf : RadiallyAntitone f) (x y z : ℝ)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    0 ≤ (k (x-z)-k (y-z))*(f z-f (x+y-z)) := by
  by_cases hz : 2*z ≤ x+y
  · have ha : |x-z| ≤ |y-z| := sq_le_sq.mp (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x+y-2*z by linarith)])
    have hb : |z| ≤ |x+y-z| := sq_le_sq.mp (by
      nlinarith [mul_nonneg (show 0 ≤ x+y by linarith) (show 0 ≤ x+y-2*z by linarith)])
    exact mul_nonneg (sub_nonneg.mpr (hk _ _ ha)) (sub_nonneg.mpr (hf _ _ hb))
  · have ha : |y-z| ≤ |x-z| := sq_le_sq.mp (by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2*z-x-y by linarith)])
    have hb : |x+y-z| ≤ |z| := sq_le_sq.mp (by
      nlinarith [mul_nonneg (show 0 ≤ x+y by linarith) (show 0 ≤ 2*z-x-y by linarith)])
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hk _ _ ha)) (sub_nonpos.mpr (hf _ _ hb))

/-- The usual bounded convolution has its equivalent translated-kernel
integral expression. -/
theorem boundedConvolutionValue_translated_kernel (k : ℝ → ℝ) (f : BoundedRealFunction) (x : ℝ) :
    boundedConvolutionValue k f x=∫ v : ℝ, k (x-v)*f v := by
  have hh := integral_sub_left_eq_self (fun v : ℝ => k v*f (x-v)) volume x
  have hid : (fun v : ℝ => k (x-v)*f (x-(x-v)))=(fun v : ℝ => k (x-v)*f v) := by
    funext v
    rw [show x-(x-v)=v by ring]
  change (∫ v : ℝ, k (x-v)*f (x-(x-v)))=boundedConvolutionValue k f x at hh
  rw [hid] at hh
  exact hh.symm

/-- Convolution preserves radial monotonicity on the real line. The
proof is ordinary integrable pairing, without a rearrangement axiom. -/
theorem boundedConvolution_radiallyAntitone (k : ℝ → ℝ) (hk : Integrable k)
    (hkr : RadiallyAntitone k) (f : BoundedRealFunction) (hfr : RadiallyAntitone (fun u => f u)) :
    RadiallyAntitone (fun u => boundedConvolution k hk f u) := by
  have hi (x : ℝ) : Integrable (fun v : ℝ => k (x-v)*f v) :=
    (hk.comp_sub_left x).mul_bdd f.continuous.aestronglyMeasurable (Eventually.of_forall f.norm_coe_le_norm)
  have happ (x : ℝ) : boundedConvolution k hk f x=∫ v : ℝ, k (x-v)*f v :=
    boundedConvolutionValue_translated_kernel k f x
  apply radiallyAntitone_of_even_positive_half
  · intro x
    rw [happ,happ]
    have he := integral_sub_left_eq_self (fun v : ℝ => k (-x-v)*f v) volume 0
    have hident : (fun v : ℝ => k (-x-(0-v))*f (0-v))=(fun v : ℝ => k (x-v)*f v) := by
      funext v
      rw [zero_sub,show -x-(-v)=-(x-v) by ring,hkr.even,hfr.even]
    change (∫ v : ℝ, k (-x-(0-v))*f (0-v))=∫ v : ℝ, k (-x-v)*f v at he
    rw [hident] at he
    exact he.symm
  · intro x y hx hxy
    let g : ℝ → ℝ := fun v => (k (x-v)-k (y-v))*f v
    have hg : Integrable g := by
      simpa only [g,sub_mul,Pi.sub_apply] using! (hi x).sub (hi y)
    have hp (v : ℝ) : 0 ≤ g v+g (x+y-v) := by
      have hident : g v+g (x+y-v)=(k (x-v)-k (y-v))*(f v-f (x+y-v)) := by
        dsimp [g]
        rw [show x-(x+y-v)=-(y-v) by ring,show y-(x+y-v)=-(x-v) by ring,hkr.even,hkr.even]
        ring
      rw [hident]
      exact radial_convolution_pair_nonneg k (fun u => f u) hkr hfr x y v hx hxy
    have hInt : (0 : ℝ) ≤ ∫ v : ℝ, g v+g (x+y-v) := integral_nonneg hp
    rw [integral_add hg (hg.comp_sub_left (x+y)),integral_sub_left_eq_self g volume (x+y)] at hInt
    have hIntg : (∫ v : ℝ, g v)=boundedConvolution k hk f x-boundedConvolution k hk f y := by
      rw [happ,happ,← integral_sub (hi x) (hi y)]
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => by dsimp [g]; ring)
    rw [hIntg] at hInt
    linarith

/-- Radial monotonicity survives the actual norm-convergent operator
Neumann series when it is preserved by each application. -/
theorem radial_operator_neumann (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1)
    (hpres : ∀ f : BoundedRealFunction, RadiallyAntitone (fun u => f u) → RadiallyAntitone (fun u => A f u))
    (f : BoundedRealFunction) (hf : RadiallyAntitone (fun u => f u)) :
    RadiallyAntitone (fun u => (∑' m : ℕ, A^m) f u) := by
  have hs : Summable (fun m : ℕ => A^m) := summable_geometric_of_norm_lt_one (x := A) hA
  have hp (m : ℕ) : RadiallyAntitone (fun u => (A^m) f u) := by
    induction m with
    | zero => simpa only [pow_zero,one_apply_eq_self] using hf
    | succ m ih => rw [pow_succ']; exact hpres _ ih
  intro u v huv
  have he (x : ℝ) : (∑' m : ℕ, (A^m) f) x=∑' m : ℕ, (A^m) f x :=
    (BoundedContinuousFunction.evalCLM ℝ x).map_tsum (summable_apply hs f)
  change (∑' m : ℕ, A^m) f v ≤ (∑' m : ℕ, A^m) f u
  rw [tsum_apply hs f,he u,he v]
  exact ((BoundedContinuousFunction.evalCLM ℝ v).summable (summable_apply hs f)).tsum_le_tsum
    (fun m => hp m u v huv)
    ((BoundedContinuousFunction.evalCLM ℝ u).summable (summable_apply hs f))
/-- A positive hyperbolic-denominator profile decreases with distance
from the origin. -/
theorem phase_fraction_radiallyAntitone (theta A : ℝ) (hs : Real.sin theta ≠ 0) (hA : 0 ≤ A) :
    RadiallyAntitone (fun u => A/(Real.pi*(Real.cosh (2*u)-Real.cos (2*theta)))) := by
  intro u v huv
  have hc : Real.cosh (2*u) ≤ Real.cosh (2*v) := Real.cosh_le_cosh.mpr (by
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using mul_le_mul_of_nonneg_left huv (by norm_num : (0 : ℝ) ≤ 2))
  apply div_le_div_of_nonneg_left hA (mul_pos Real.pi_pos (phase_denominator_pos theta u hs))
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hc _) Real.pi_pos.le

theorem kernelS_radiallyAntitone (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    RadiallyAntitone (kernelS lam) := by
  have hs : Real.sin (lam/2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hh := phase_fraction_radiallyAntitone (lam/2) (Real.sin lam) hs (Real.sin_pos_of_pos_of_lt_pi h0 hpi).le
  intro u v huv
  rw [kernelS_eq_phaseDensity,kernelS_eq_phaseDensity]
  simpa only [phaseDensity,show 2*(lam/2)=lam by ring] using hh u v huv

theorem negative_kernelK_radiallyAntitone (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    RadiallyAntitone (fun u => -kernelK lam u) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have hc : Real.cos lam ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith)
  have hA : 0 ≤ -Real.sin (2*lam) := by
    rw [Real.sin_two_mul]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hs.le) hc)
  simpa only [kernelK,phaseDensity,neg_div] using phase_fraction_radiallyAntitone lam (-Real.sin (2*lam)) hs.ne' hA

theorem negative_physicalFullOperator_radial (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (f : BoundedRealFunction)
    (hf : RadiallyAntitone (fun u => f u)) :
    RadiallyAntitone (fun u => (-(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))) f u) := by
  have he : (fun u => (-(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))) f u)=
      (fun u => boundedConvolution (fun t => -kernelK lam t) (kernelK_integrable lam h0 hpi).neg f u) := by
    funext u
    change -(∫ t : ℝ, kernelK lam t*f (u-t))=∫ t : ℝ, (-kernelK lam t)*f (u-t)
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by ring)
  rw [he]
  exact boundedConvolution_radiallyAntitone _ (kernelK_integrable lam h0 hpi).neg
    (negative_kernelK_radiallyAntitone lam hhalf hpi) f hf

/-- The actual inverse-defined full-line density is radially decreasing.
No Fourier formula is assumed. -/
theorem fullLineDensityFunction_radiallyAntitone (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    RadiallyAntitone (fun u => fullLineDensityFunction lam h0 hpi u) := by
  let A := -(boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))
  have hA : ‖A‖ < 1 := (norm_neg (boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))).trans_lt
    ((boundedConvolutionOperator_norm_bound (kernelK lam) (kernelK_integrable lam h0 hpi)).trans_lt (kernelK_L1_mass_lt_one lam h0 hpi))
  change RadiallyAntitone (fun u => (∑' m : ℕ, A^m) (physicalSourceFunction lam h0 hpi) u)
  apply radial_operator_neumann A hA (negative_physicalFullOperator_radial lam h0 hhalf hpi)
  intro u v huv
  change physicalSourceFunction lam h0 hpi v ≤ physicalSourceFunction lam h0 hpi u
  rw [physicalSourceFunction_apply,physicalSourceFunction_apply]
  exact kernelS_radiallyAntitone lam h0 hpi u v huv

end
end SixVertex
