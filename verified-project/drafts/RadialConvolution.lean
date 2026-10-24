import SixVertex.PositiveNeumann

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

end
end SixVertex
