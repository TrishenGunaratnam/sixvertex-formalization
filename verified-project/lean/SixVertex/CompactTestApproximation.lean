import SixVertex.RegularFillingQuadrature
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace SixVertex
noncomputable section
open Set MeasureTheory
open scoped NNReal

/-- A compactly supported continuous real test has genuine compactly
supported Lipschitz approximants in the uniform norm. -/
theorem exists_compact_lipschitz_test_approximation (phi : BoundedRealFunction)
    (A : ℝ) (hA : 0 ≤ A) (hs : ∀ x, x ∉ Icc (-A) A → phi x=0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (psi : BoundedRealFunction) (K : ℝ≥0), LipschitzWith K (fun x => psi x) ∧
      (∀ x, x ∉ Icc (-(A+1)) (A+1) → psi x=0) ∧ ‖phi-psi‖ ≤ eps := by
  let B := A+1
  have hB : 0 < B := by dsimp [B]; linarith
  obtain ⟨p,hnear⟩ := exists_polynomial_near_of_continuousOn (-B) B (fun x => phi x)
    phi.continuous.continuousOn eps heps
  let clip : ℝ → ℝ := fun x => max (-B) (min B x)
  have hclip : LipschitzWith 1 clip := (LipschitzWith.id.const_min B).const_max (-B)
  have hmem (x : ℝ) : clip x ∈ Icc (-B) B :=
    ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
  have hclip_eq (x : ℝ) (hx : x ∈ Icc (-B) B) : clip x=x := by
    dsimp [clip]
    rw [min_eq_right hx.2,max_eq_right hx.1]
  let pp : ℝ → ℝ := fun x => p.eval (clip x)
  let F : ℝ := eps+‖phi‖
  have hF : 0 ≤ F := add_nonneg heps.le (norm_nonneg _)
  have hppBound (x : ℝ) : |pp x| ≤ F := by
    have hh := abs_add_le (pp x-phi (clip x)) (phi (clip x))
    rw [sub_add_cancel] at hh
    exact hh.trans (add_le_add (hnear (clip x) (hmem x)).le
      (by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm (clip x)))
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn p.derivative.continuous.continuousOn
  let K : ℝ≥0 := ⟨max D 0,le_max_right _ _⟩
  have hK : (K : ℝ)=max D 0 := rfl
  have hppLip (x y : ℝ) : |pp x-pp y| ≤ (K : ℝ)*|x-y| := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v (_ : v ∈ Icc (-B) B) => (p.hasDerivAt v).hasDerivWithinAt)
      (fun v (hv : v ∈ Icc (-B) B) => (hD v hv).trans (le_max_left D 0))
      (convex_Icc (-B) B) (hmem y) (hmem x)
    have hc : |clip x-clip y| ≤ |x-y| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hclip.dist_le_mul x y
    have hp : |pp x-pp y| ≤ (K : ℝ)*|clip x-clip y| := by
      change |p.eval (clip x)-p.eval (clip y)| ≤ (K : ℝ)*|clip x-clip y|
      rw [hK]
      simpa only [Real.norm_eq_abs] using hh
    exact hp.trans (mul_le_mul_of_nonneg_left hc K.coe_nonneg)
  let eta : ℝ → ℝ := fun x => max 0 (min 1 (B-|x|))
  have hraw : LipschitzWith 1 (fun x : ℝ => B-|x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(B-|x|)-(B-|y|)| ≤ ((1 : ℝ≥0) : ℝ)*|x-y|
    have heq : (B-|x|)-(B-|y|)=-(|x|-|y|) := by ring
    rw [heq,abs_neg]
    simpa only [NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y
  have hetaLip : LipschitzWith 1 eta := (hraw.const_min 1).const_max 0
  have heta0 (x : ℝ) : 0 ≤ eta x := le_max_left _ _
  have heta1 (x : ℝ) : eta x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hetaAbs (x : ℝ) : |eta x| ≤ 1 := by rw [abs_of_nonneg (heta0 x)]; exact heta1 x
  have hetaDiff (x y : ℝ) : |eta x-eta y| ≤ |x-y| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hetaLip.dist_le_mul x y
  have hetaCore (x : ℝ) (hx : x ∈ Icc (-A) A) : eta x=1 := by
    have hab : |x| ≤ A := abs_le.mpr hx
    dsimp [eta]
    rw [min_eq_left (by dsimp [B]; linarith),max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  have hetaOut (x : ℝ) (hx : x ∉ Icc (-B) B) : eta x=0 := by
    have hab : B < |x| := lt_of_not_ge (fun hh => hx (abs_le.mp hh))
    exact max_eq_left ((min_le_right 1 (B-|x|)).trans (by linarith))
  have hcont : Continuous (fun x => pp x*eta x) :=
    (p.continuous.comp hclip.continuous).mul hetaLip.continuous
  let psi := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => pp x*eta x) hcont F
    (fun x => by
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul (hppBound x) (hetaAbs x) (abs_nonneg _) hF).trans_eq (mul_one F))
  let S : ℝ≥0 := ⟨(K : ℝ)+F,add_nonneg K.coe_nonneg hF⟩
  refine ⟨psi,S,?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change |pp x*eta x-pp y*eta y| ≤ ((K : ℝ)+F)*|x-y|
    have hid : pp x*eta x-pp y*eta y=pp x*(eta x-eta y)+eta y*(pp x-pp y) := by ring
    rw [hid]
    have ht := abs_add_le (pp x*(eta x-eta y)) (eta y*(pp x-pp y))
    rw [abs_mul,abs_mul] at ht
    have h1 := mul_le_mul (hppBound x) (hetaDiff x y) (abs_nonneg _) hF
    have h2 := mul_le_mul (hetaAbs y) (hppLip x y) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [ht,h1,h2]
  · intro x hx
    change pp x*eta x=0
    rw [hetaOut x hx,mul_zero]
  · apply (BoundedContinuousFunction.norm_le heps.le).mpr
    intro x
    change |phi x-pp x*eta x| ≤ eps
    by_cases hx : x ∈ Icc (-B) B
    · have hphiEta : phi x*(1-eta x)=0 := by
        by_cases hcore : x ∈ Icc (-A) A
        · rw [hetaCore x hcore,sub_self,mul_zero]
        · rw [hs x hcore,zero_mul]
      have hid : phi x-pp x*eta x=(phi x-pp x)*eta x := by nlinarith only [hphiEta]
      rw [hid,abs_mul]
      have hn : |phi x-pp x| ≤ eps := by
        dsimp [pp]
        rw [hclip_eq x hx,abs_sub_comm]
        exact (hnear x hx).le
      exact (mul_le_mul hn (hetaAbs x) (abs_nonneg _) heps.le).trans_eq (mul_one eps)
    · have hphi : phi x=0 := by
        apply hs
        intro hcore
        apply hx
        constructor <;> dsimp [B] <;> linarith [hcore.1,hcore.2]
      rw [hphi,hetaOut x hx,mul_zero,sub_self,abs_zero]
      exact heps.le

end
end SixVertex
