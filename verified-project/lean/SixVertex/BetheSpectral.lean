import SixVertex.BetheOnShell
import SixVertex.BetheParity

namespace SixVertex

noncomputable def betheFProduct {n : ℕ} (lam : ℝ) (Y : Fin n → ℝ) (x : ℂ) : ℂ :=
  ∏ j, betheF (Complex.I*lam) ((Y j : ℂ)-x)

/-- The factorized meromorphic expression tau from the manuscript. -/
noncomputable def betheTau {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (x : ℂ) : ℂ :=
  Complex.exp (Complex.I*twist) * vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) x L *
    betheFProduct lam Y x * (1+Complex.exp (-2*Complex.I*twist)*betheQ lam b L Y x)

theorem tau_factorization (a l P Q z w v : ℂ) (ha : a ≠ 0) (hP : P ≠ 0)
    (hw : z*w = v) : z*a*P*(1+w*(l/a*(Q/P))) = z*a*P+v*l*Q := by
  field_simp [ha,hP]
  rw [← hw]
  ring

theorem betheTau_eq_abaEigenvalue {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (twist : ℝ) (x : ℂ)
    (hx : x ∉ rootSet Y) (hreg : BetheRegular (Complex.I*lam) (insert x (rootSet Y)))
    (ha : vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) x L ≠ 0) :
    betheTau lam b L Y twist x =
      abaEigenvalue (Complex.I*lam) (fun j => (b j : ℂ)) L twist (rootSet Y) x := by
  classical
  let t : ℂ := Complex.I*lam
  have hP : (∏ p ∈ rootSet Y, betheF t (p-x)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hpx : p ≠ x := fun he => hx (he ▸ hp)
    exact div_ne_zero (hreg.2 p (Finset.mem_insert_of_mem hp) x (Finset.mem_insert_self _ _))
      (hreg.1 p (Finset.mem_insert_of_mem hp) x (Finset.mem_insert_self _ _) hpx)
  have hprod : (∏ j, Complex.sinh (x-Y j+t) / Complex.sinh (x-Y j-t)) =
      (∏ p ∈ rootSet Y, betheF t (x-p)) / ∏ p ∈ rootSet Y, betheF t (p-x) := by
    rw [← prod_rootSet Y hY (fun p => Complex.sinh (x-p+t) / Complex.sinh (x-p-t)),
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hxp : x ≠ p := fun he => hx (he.symm ▸ hp)
    rw [shifted_ratio_as_f t _ (hreg.1 x (Finset.mem_insert_self _ _) p
      (Finset.mem_insert_of_mem hp) hxp)]
    congr 2
    ring
  have he : Complex.exp (Complex.I*twist) * Complex.exp (-2*Complex.I*twist) =
      Complex.exp (-Complex.I*twist) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold betheTau betheQ betheFProduct abaEigenvalue
  rw [← prod_rootSet Y hY (fun p => betheF t (p-x)), hprod]
  exact tau_factorization _ _ _ _ _ _ _ ha hP he

/-- The on-shell standard-row eigenvector equation at every generic complex
spectral value. An entire extension is constructed separately below. -/
theorem onShell_standard_eigenvector {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist) (x : ℂ)
    (hx : x ∉ rootSet Y) (hreg : BetheRegular (Complex.I*lam) (insert x (rootSet Y)))
    (ha : vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) x L ≠ 0) :
    twistedStandardRow (Complex.I*lam) (fun j => (b j : ℂ)) L twist x *
      betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
        (fun j => (b j : ℂ)) L (rootSet Y) =
    betheTau lam b L Y twist x •
      betheState (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
        (fun j => (b j : ℂ)) L (rootSet Y) := by
  rw [betheTau_eq_abaEigenvalue lam b L Y hY twist x hx hreg ha]
  exact balancedRoots_eigenvector _ _ _ _ _ _
    (onShell_balancedRoots lam h0 hpi b L Y hY twist hShell) x hx hreg

end SixVertex
