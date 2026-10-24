import SixVertex.BethePhaseData
import SixVertex.BetheEigenvectors

namespace SixVertex

noncomputable def rootSet {n : ℕ} (Y : Fin n → ℝ) : Finset ℂ :=
  Finset.univ.image (fun j => (Y j : ℂ))

theorem rootSet_card {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y) :
    (rootSet Y).card = n := by
  classical
  rw [rootSet, Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro i j hij
    exact hY (Complex.ofReal_inj.mp hij)

theorem prod_rootSet {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y) (f : ℂ → ℂ) :
    (∏ p ∈ rootSet Y, f p) = ∏ j, f (Y j) := by
  classical
  exact Finset.prod_image (fun i _ j _ hij => hY (Complex.ofReal_inj.mp hij))

theorem betheF_reverse (t z : ℂ) :
    betheF t (-z) = Complex.sinh (z-t) / Complex.sinh z := by
  unfold betheF
  rw [show -z+t = -(z-t) by ring, Complex.sinh_neg, Complex.sinh_neg, neg_div_neg_eq]

theorem shifted_ratio_as_f (t z : ℂ) (hz : Complex.sinh z ≠ 0) :
    Complex.sinh (z+t) / Complex.sinh (z-t) = betheF t z / betheF t (-z) := by
  rw [betheF_reverse, betheF, div_div_div_cancel_right₀ hz]

theorem vacuumA_real_ne_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) u L ≠ 0 := by
  rw [vacuumA_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply div_ne_zero _ (physical_deformation_ne_zero lam h0 hpi)
  have hs : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hn := sinh_real_shift_ne_zero (u-b j) (lam/2) hs
  convert hn using 1 <;> push_cast <;> congr 1 <;> ring

theorem real_rootSet_regular {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Y : Fin n → ℝ) : BetheRegular (Complex.I*lam) (rootSet Y) := by
  classical
  constructor
  · intro p hp q hq hn
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hq
    have hy : Y j-Y k ≠ 0 := by intro he; apply hn; exact congrArg Complex.ofReal (sub_eq_zero.mp he)
    have hs : Real.sinh (Y j-Y k) ≠ 0 := by
      intro h
      exact hy (Real.sinh_eq_zero.mp h)
    simpa only [Complex.ofReal_sinh, Complex.ofReal_sub] using Complex.ofReal_ne_zero.mpr hs
  · intro p hp q hq
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hq
    simpa only [Complex.ofReal_sub] using
      sinh_real_shift_ne_zero (Y j-Y k) lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

/-- On-shell equations expressed as cancellation of unwanted root replacements. -/
theorem onShell_balancedRoots {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist) :
    BalancedRoots (Complex.I*lam) (fun j => (b j : ℂ)) L twist (rootSet Y) := by
  classical
  intro p hp
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
  let t : ℂ := Complex.I*lam
  let a : ℂ := vacuumA t (fun j => (b j : ℂ)) (Y j) L
  let l : ℂ := vacuumL t (fun j => (b j : ℂ)) (Y j) L
  let P : ℂ := ∏ u ∈ (rootSet Y).erase (Y j : ℂ), betheF t (u-Y j)
  let Q : ℂ := ∏ u ∈ (rootSet Y).erase (Y j : ℂ), betheF t ((Y j : ℂ)-u)
  have hp : (Y j : ℂ) ∈ rootSet Y := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hreg := real_rootSet_regular lam h0 hpi Y
  have hPn : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    have hup := Finset.mem_erase.mp hu
    exact div_ne_zero (hreg.2 u hup.2 (Y j) hp)
      (hreg.1 u hup.2 (Y j) hp hup.1)
  have han : a ≠ 0 := vacuumA_real_ne_zero lam h0 hpi b L (Y j)
  have hq : betheQ lam b L Y (Y j) = -(l*Q)/(a*P) := by
    unfold betheQ
    rw [← prod_rootSet Y hY (fun u => Complex.sinh ((Y j : ℂ)-u+t) / Complex.sinh ((Y j : ℂ)-u-t))]
    rw [← Finset.mul_prod_erase (rootSet Y)
      (fun u => Complex.sinh ((Y j : ℂ)-u+t) / Complex.sinh ((Y j : ℂ)-u-t)) hp]
    have ht := physical_deformation_ne_zero lam h0 hpi
    have ht' : Complex.sinh t ≠ 0 := ht
    have hs : Complex.sinh (-t) = -Complex.sinh t := Complex.sinh_neg t
    simp only [sub_self, zero_add, zero_sub, hs, div_neg_eq_neg_div, div_self ht']
    have he : (∏ u ∈ (rootSet Y).erase (Y j : ℂ),
        Complex.sinh ((Y j : ℂ)-u+t) / Complex.sinh ((Y j : ℂ)-u-t)) = Q/P := by
      dsimp [P,Q]
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro u hu
      have hup := Finset.mem_erase.mp hu
      have hz := hreg.1 (Y j) hp u hup.2 hup.1.symm
      rw [shifted_ratio_as_f t _ hz]
      congr 2
      ring
    rw [he]
    dsimp [a,l,t]
    ring
  have hbal : l*Q = Complex.exp (2*Complex.I*twist) * (a*P) := by
    have h := hShell j
    rw [hq] at h
    field_simp [han,hPn] at h
    linear_combination -h
  have he : Complex.exp (-Complex.I*twist) * Complex.exp (2*Complex.I*twist) =
      Complex.exp (Complex.I*twist) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  change Complex.exp (Complex.I*twist)*a*P = Complex.exp (-Complex.I*twist)*l*Q
  linear_combination -(Complex.exp (-Complex.I*twist))*hbal - (a*P)*he

end SixVertex
