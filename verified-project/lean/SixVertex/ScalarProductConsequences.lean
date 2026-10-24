import SixVertex.ScalarProductLimits

namespace SixVertex
open Filter Topology

/-- The Gaudin norm follows from the generic Slavnov assumption and the proved
simultaneous complex limit. It is not part of that assumption. -/
theorem gaudin_norm_residue {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hSlavnov : SlavnovSourceIdentity lam b L Y twist) :
    algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) =
      (-2*(Real.pi : ℂ)*Complex.I)^n *
      (∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L) *
      (∏ k, -Complex.sinh (Complex.I*lam)*rootVacuumFactor lam b L Y k) *
      (complexGaudin lam b L Y).det := by
  have hh := slavnov_partial_coincidence lam h0 hpi b L hEven Y hY twist hShell hSlavnov
    ∅ (fun k => (Y k : ℂ)) (by simp) (by simp)
  have hI : replaceColumns (1 : Matrix (Fin n) (Fin n) ℂ) (scalarCauchy Y (fun k => (Y k : ℂ))) ∅ = 1 := by
    ext i j
    simp [replaceColumns]
  have hG : replaceColumns (complexGaudin lam b L Y)
      (scalarSourceMatrix lam b L Y twist (fun k => (Y k : ℂ))) ∅ = complexGaudin lam b L Y := by
    ext i j
    simp [replaceColumns]
  rw [hI, hG, Matrix.det_one, mul_one] at hh
  simpa only [Finset.notMem_empty, ite_false] using hh

/-- The paper's exact norm prefactor, including the ordered pair product. -/
noncomputable def gaudinNormPrefactor {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : ℂ :=
  (2*(Real.pi : ℂ)*Complex.I*Complex.sinh (Complex.I*lam))^n *
    (∏ j, vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L *
      vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L) *
    ∏ k, ∏ j ∈ Finset.univ.erase k, betheF (Complex.I*lam) ((Y j : ℂ)-Y k)

theorem gaudin_norm_exact {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hSlavnov : SlavnovSourceIdentity lam b L Y twist) :
    algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) =
      gaudinNormPrefactor lam b L Y * (complexGaudin lam b L Y).det := by
  rw [gaudin_norm_residue lam h0 hpi b L hEven Y hY twist hShell hSlavnov]
  unfold rootVacuumFactor gaudinNormPrefactor
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he : (2*(Real.pi : ℂ)*Complex.I*Complex.sinh (Complex.I*lam))^n =
      (-2*(Real.pi : ℂ)*Complex.I)^n * (-Complex.sinh (Complex.I*lam))^n := by
    rw [← mul_pow]
    congr 1
    ring
  rw [he]
  ring

/-- No vacuum factor or root interaction in the norm vanishes on the real slice. -/
theorem rootVacuumFactor_ne_zero {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y) (k : Fin n) :
    rootVacuumFactor lam b L Y k ≠ 0 := by
  apply mul_ne_zero (vacuumA_real_ne_zero lam h0 hpi b L (Y k))
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply div_ne_zero
  · simpa only [Complex.ofReal_sub] using
      sinh_real_shift_ne_zero (Y j-Y k) lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  · exact real_sinh_sub_ne Y hY (Finset.mem_erase.mp hj).1.symm

theorem vacuumL_real_ne_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) u L ≠ 0 := by
  rw [vacuumL_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply div_ne_zero _ (physical_deformation_ne_zero lam h0 hpi)
  have hs : Real.sin (-(lam/2)) ≠ 0 := by
    simpa using (Real.sin_pos_of_pos_of_lt_pi (show 0 < lam/2 by linarith)
      (show lam/2 < Real.pi by linarith [Real.pi_pos])).ne'
  have hn := sinh_real_shift_ne_zero (u-b j) (-(lam/2)) hs
  convert hn using 1 <;> push_cast <;> congr 1 <;> ring

theorem complexGaudin_det {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) :
    (complexGaudin lam b L Y).det = ((gaudinMatrix lam b L Y).det : ℂ) := by
  exact (RingHom.map_det Complex.ofRealHom _).symm

theorem gaudin_norm_ne_zero {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hSlavnov : SlavnovSourceIdentity lam b L Y twist) (hdet : (gaudinMatrix lam b L Y).det ≠ 0) :
    algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) ≠ 0 := by
  rw [gaudin_norm_residue lam h0 hpi b L hEven Y hY twist hShell hSlavnov]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero _ (by exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      · exact Finset.prod_ne_zero_iff.mpr (fun j _ => vacuumL_real_ne_zero lam h0 hpi b L (Y j))
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact mul_ne_zero (neg_ne_zero.mpr (physical_deformation_ne_zero lam h0 hpi))
        (rootVacuumFactor_ne_zero lam h0 hpi b L Y hY k)
  · rw [complexGaudin_det]
    exact Complex.ofReal_ne_zero.mpr hdet

/-- Inversion of G diag(ell)=B, with all nonsingularity hypotheses explicit. -/
theorem inverse_column_weights {I : Type*} [Fintype I] [DecidableEq I]
    (G : Matrix I I ℂ) (ell : I → ℂ) (hG : G.det ≠ 0) (hell : ∀ j, ell j ≠ 0) :
    G⁻¹ = Matrix.diagonal ell * (G * Matrix.diagonal ell)⁻¹ := by
  have hB : (G * Matrix.diagonal ell).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero hG (Finset.prod_ne_zero_iff.mpr (fun j _ => hell j))
  calc
    G⁻¹ = G⁻¹ * ((G * Matrix.diagonal ell) * (G * Matrix.diagonal ell)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB), mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG), one_mul]

/-- Product cancellation retains only the replaced slots. -/
theorem product_replacement_ratio {I : Type*} [Fintype I] [DecidableEq I]
    (H : Finset I) (a r : I → ℂ) (hr : ∀ i, r i ≠ 0) :
    (∏ i, if i ∈ H then a i else r i) / (∏ i, r i) = ∏ i ∈ H, a i/r i := by
  classical
  rw [← Finset.prod_div_distrib]
  have he : (fun i => (if i ∈ H then a i else r i)/r i) =
      (fun i => if i ∈ H then a i/r i else 1) := by
    funext i
    split_ifs <;> simp_all
  rw [he, Finset.prod_ite_mem_eq]

/-- The exact scalar ratio after partial pole cancellation. -/
theorem deleted_scalar_product {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hSlavnov : SlavnovSourceIdentity lam b L Y twist) (hdet : (gaudinMatrix lam b L Y).det ≠ 0)
    (H : Finset (Fin n)) (V : Fin n → ℂ)
    (hV : ∀ k ∈ H, SourceRegular lam b L Y (V k))
    (hcross : ∀ k ∈ H, ∀ j, Complex.sinh (V k-Y j) ≠ 0)
    (hC : ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det ≠ 0) :
    algebraicScalarProduct lam b L Y (fun k => if k ∈ H then V k else (Y k : ℂ)) /
      algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) =
      ((-Complex.sinh (Complex.I*lam))^H.card)⁻¹ *
      ((∏ k ∈ H, extractedVacuum lam b L Y (V k)) / (∏ k ∈ H, rootVacuumFactor lam b L Y k)) *
      (((complexGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y twist V).submatrix
        (fun i : H => i.val) (fun j : H => j.val)).det /
      ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det := by
  classical
  let G := complexGaudin lam b L Y
  let M := scalarSourceMatrix lam b L Y twist V
  let R := fun k => -Complex.sinh (Complex.I*lam)*rootVacuumFactor lam b L Y k
  let a := fun k => extractedVacuum lam b L Y (V k)
  let c := (-2*(Real.pi : ℂ)*Complex.I)^n *
      ∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L
  have hR : ∀ k, R k ≠ 0 := fun k => mul_ne_zero
    (neg_ne_zero.mpr (physical_deformation_ne_zero lam h0 hpi))
    (rootVacuumFactor_ne_zero lam h0 hpi b L Y hY k)
  have hG : G.det ≠ 0 := by
    dsimp [G]
    rw [complexGaudin_det]
    exact Complex.ofReal_ne_zero.mpr hdet
  have hN := gaudin_norm_ne_zero lam h0 hpi b L hEven Y hY twist hShell hSlavnov hdet
  have hn := gaudin_norm_residue lam h0 hpi b L hEven Y hY twist hShell hSlavnov
  change algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) = c*(∏ k, R k)*G.det at hn
  have hc : c ≠ 0 := by
    intro hz
    apply hN
    rw [hn, hz, zero_mul, zero_mul]
  have hr := Finset.prod_ne_zero_iff.mpr (fun k (_ : k ∈ Finset.univ) => hR k)
  have hp := slavnov_partial_coincidence lam h0 hpi b L hEven Y hY twist hShell hSlavnov H V hV hcross
  rw [det_replace_identity] at hp
  change algebraicScalarProduct lam b L Y (fun k => if k ∈ H then V k else (Y k : ℂ)) *
    ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det =
      c*(∏ k, if k ∈ H then a k else R k)*(replaceColumns G M H).det at hp
  have hreplace := det_replace_columns G M hG H
  have hreplace' := (div_eq_iff hG).mp hreplace
  have hratio : (∏ k, if k ∈ H then a k else R k)/(∏ k, R k) =
      ((-Complex.sinh (Complex.I*lam))^H.card)⁻¹ *
      ((∏ k ∈ H, a k)/(∏ k ∈ H, rootVacuumFactor lam b L Y k)) := by
    rw [product_replacement_ratio H a R hR]
    dsimp [R]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  rw [hn]
  have hsexpr := (eq_div_iff hC).mpr hp
  rw [hsexpr, hreplace']
  dsimp [G, M] at *
  rw [← hratio]
  field_simp
  <;> ring

end SixVertex
