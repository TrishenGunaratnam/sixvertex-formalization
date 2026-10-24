import SixVertex.ReplacementSlots
import SixVertex.NormalizedWords

namespace SixVertex

theorem pathVacuumBase_root {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (j : Fin n) :
    pathVacuumBase (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (Y j) =
      rootVacuumFactor lam b L Y j := by
  classical
  have hinj : Function.Injective (fun j => (Y j : ℂ)) := fun i j h => hY (Complex.ofReal_injective h)
  unfold pathVacuumBase rootVacuumFactor rootSet
  rw [← Finset.image_erase hinj, Finset.prod_image]
  exact fun i _ j _ h => hinj h

/-- A multiplicative replacement identity, valid even when factors vanish. -/
theorem prod_replacement_balance {n : ℕ} (H : Finset (Fin n)) (f g : Fin n → ℂ) :
    (∏ j, if j ∈ H then g j else f j)*(∏ j ∈ H, f j) =
      (∏ j, f j)*(∏ j ∈ H, g j) := by
  classical
  rw [← Fintype.prod_ite_mem H f, ← Fintype.prod_ite_mem H g, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h : j ∈ H <;> simp [h,mul_comm]

/-- The potential at a replacement endpoint balances exactly the deleted
root bases and the extracted bases of the surviving arguments. -/
theorem replacement_potential_balance {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (H : Finset (Fin n)) (V : Fin n → ℂ)
    (R : Fin n → ℂ) (hR : Function.Injective R)
    (hslots : ∀ j, R j = if j ∈ H then V j else (Y j : ℂ))
    (hnew : ∀ j ∈ H, V j ∉ rootSet Y) :
    vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (Finset.univ.image R) *
      (∏ j ∈ H, rootVacuumFactor lam b L Y j) =
    vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (rootSet Y) *
      (∏ j ∈ H, extractedVacuum lam b L Y (V j)) := by
  classical
  have hRprod : vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y)
      (Finset.univ.image R) =
      ∏ j, if j ∈ H then extractedVacuum lam b L Y (V j) else rootVacuumFactor lam b L Y j := by
    unfold vacuumPotential
    rw [Finset.prod_image (fun i _ j _ h => hR h)]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hslots]
    by_cases hh : j ∈ H
    · simp only [if_pos hh]
      exact pathVacuumBase_new lam b L Y hY (V j) (hnew j hh)
    · simp only [if_neg hh]
      exact pathVacuumBase_root lam b L Y hY j
  have hYprod : vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (rootSet Y) =
      ∏ j, rootVacuumFactor lam b L Y j := by
    unfold vacuumPotential
    rw [prod_rootSet Y hY]
    exact Finset.prod_congr rfl (fun j hj => pathVacuumBase_root lam b L Y hY j)
  rw [hRprod,hYprod]
  exact prod_replacement_balance H _ _

/-- The cancellation in the paper is an exact complex field identity; no
absolute values or termwise limit have been substituted for it. -/
theorem replacement_potential_cancel {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (H : Finset (Fin n)) (V R : Fin n → ℂ) (hR : Function.Injective R)
    (hslots : ∀ j, R j = if j ∈ H then V j else (Y j : ℂ))
    (hnew : ∀ j ∈ H, V j ∉ rootSet Y)
    (ha : ∀ j ∈ H, extractedVacuum lam b L Y (V j) ≠ 0) :
    vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (rootSet Y) /
      vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (Finset.univ.image R) *
      ((∏ j ∈ H, extractedVacuum lam b L Y (V j))/(∏ j ∈ H, rootVacuumFactor lam b L Y j)) = 1 := by
  have hb := replacement_potential_balance lam b L Y hY H V R hR hslots hnew
  have hroot : (∏ j ∈ H, rootVacuumFactor lam b L Y j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => rootVacuumFactor_ne_zero lam h0 hpi b L Y hY j)
  have hnewprod : (∏ j ∈ H, extractedVacuum lam b L Y (V j)) ≠ 0 := Finset.prod_ne_zero_iff.mpr ha
  have hYpot : vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y) (rootSet Y) ≠ 0 := by
    unfold vacuumPotential
    rw [prod_rootSet Y hY]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [pathVacuumBase_root lam b L Y hY]
    exact rootVacuumFactor_ne_zero lam h0 hpi b L Y hY j
  have hRpot : vacuumPotential (Complex.I*lam) (fun a => (b a : ℂ)) L (rootSet Y)
      (Finset.univ.image R) ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hb
    exact mul_ne_zero hYpot hnewprod hb.symm
  rw [div_mul_div_comm]
  exact (div_eq_one_iff_eq (mul_ne_zero hRpot hroot)).mpr hb.symm

end SixVertex
