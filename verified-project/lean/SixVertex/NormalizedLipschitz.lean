import SixVertex.NormalizedTest

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal

/-- Divide a compact Lipschitz test by the actual positive C1 density.
Clamping the reciprocal density extends the local bound globally without
requiring a positive density lower bound at infinity. -/
theorem exists_normalized_lipschitz_test (phi : BoundedRealFunction) (K : ℝ≥0)
    (hLip : LipschitzWith K (fun x => phi x))
    (rho rho' : ℝ → ℝ) (hrho : Continuous rho) (hpos : ∀ x, 0 < rho x)
    (hdrho : ∀ x, HasDerivAt rho (rho' x) x)
    (a z M C : ℝ) (haz : a ≤ z) (hM : 0 < M) (hC : 0 ≤ C)
    (hs : ∀ x, x ∉ Icc a z → phi x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ rho x)
    (hrelative : ∀ x, |rho' x| ≤ C*rho x) :
    ∃ f : BoundedRealFunction,
      (∀ x, f x=phi x/rho x) ∧
      (∀ x, x ∉ Icc a z → f x=0) ∧
      LipschitzWith ⟨((K : ℝ)+C*‖phi‖)/M,by positivity⟩ (fun x => f x) := by
  let c : ℝ → ℝ := fun x => max a (min z x)
  have hc : LipschitzWith 1 c := (LipschitzWith.id.const_min z).const_max a
  have hc_mem (x : ℝ) : c x ∈ Icc a z :=
    ⟨le_max_left _ _,max_le haz (min_le_left _ _)⟩
  have hc_eq (x : ℝ) (hx : x ∈ Icc a z) : c x=x := by
    dsimp [c]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  have hinv (x : ℝ) (hx : x ∈ Icc a z) : |-(rho' x)/(rho x)^2| ≤ C/M := by
    simpa only [zero_mul,one_mul,zero_sub,abs_zero,abs_one,mul_one,zero_add] using
      normalized_derivative_scalar_bound 1 0 (rho x) (rho' x) M C hM (hlower x hx) hC (hrelative x)
  have hinvd (x : ℝ) : HasDerivAt (fun v => (rho v)⁻¹) (-(rho' x)/(rho x)^2) x :=
    (hdrho x).inv (hpos x).ne'
  let g : ℝ → ℝ := fun x => (rho (c x))⁻¹
  have hgc : Continuous g := (hrho.comp hc.continuous).inv₀ (fun x => (hpos (c x)).ne')
  have hgb (x : ℝ) : |g x| ≤ 1/M := by
    dsimp [g]
    rw [abs_inv,abs_of_pos (hpos (c x)),← one_div]
    exact one_div_le_one_div_of_le hM (hlower _ (hc_mem x))
  have hgLip (x y : ℝ) : |g x-g y| ≤ (C/M)*|x-y| := by
    have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v (hv : v ∈ Icc a z) => (hinvd v).hasDerivWithinAt)
      (fun v (hv : v ∈ Icc a z) => by simpa only [Real.norm_eq_abs] using hinv v hv)
      (convex_Icc a z) (hc_mem y) (hc_mem x)
    have hcxy : |c x-c y| ≤ |x-y| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hc.dist_le_mul x y
    have hn' : |g x-g y| ≤ (C/M)*|c x-c y| := by
      simpa only [Real.norm_eq_abs] using hn
    exact hn'.trans (mul_le_mul_of_nonneg_left hcxy (by positivity))
  let f := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => phi x*g x)
    (phi.continuous.mul hgc) (‖phi‖/M) (fun x => by
      change |phi x*g x| ≤ ‖phi‖/M
      rw [abs_mul]
      calc
        _ ≤ ‖phi‖*(1/M) := mul_le_mul (by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm x)
          (hgb x) (abs_nonneg _) (norm_nonneg _)
        _ = _ := by ring)
  have hfeq (x : ℝ) : f x=phi x/rho x := by
    change phi x*g x=phi x/rho x
    by_cases hx : x ∈ Icc a z
    · dsimp [g]
      rw [hc_eq x hx]
      rfl
    · rw [hs x hx,zero_mul,zero_div]
  refine ⟨f,hfeq,?_,?_⟩
  · intro x hx
    rw [hfeq x,hs x hx,zero_div]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change |phi x*g x-phi y*g y| ≤ (((K : ℝ)+C*‖phi‖)/M)*|x-y|
    have hp : |phi x-phi y| ≤ (K : ℝ)*|x-y| := by
      simpa only [Real.dist_eq] using hLip.dist_le_mul x y
    have hpn : |phi y| ≤ ‖phi‖ := by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm y
    calc
      _ = |(phi x-phi y)*g x+phi y*(g x-g y)| := by congr 1; ring
      _ ≤ |(phi x-phi y)*g x|+|phi y*(g x-g y)| := abs_add_le _ _
      _ = |phi x-phi y| *|g x|+|phi y| *|g x-g y| := by rw [abs_mul,abs_mul]
      _ ≤ ((K : ℝ)*|x-y|)*(1/M)+‖phi‖*((C/M)*|x-y|) := add_le_add
        (mul_le_mul hp (hgb x) (abs_nonneg _) (by positivity))
        (mul_le_mul hpn (hgLip x y) (abs_nonneg _) (norm_nonneg _))
      _ = _ := by ring

end
end SixVertex
