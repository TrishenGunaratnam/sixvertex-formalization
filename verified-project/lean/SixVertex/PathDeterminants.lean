import SixVertex.WordExpectations
import SixVertex.DiagonalPaths

namespace SixVertex

theorem source_extractedVacuum_ne_zero {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℂ) (hu : SourceRegular lam b L Y u)
    (hcross : ∀ j, Complex.sinh (u-Y j) ≠ 0) : extractedVacuum lam b L Y u ≠ 0 := by
  unfold extractedVacuum betheFProduct
  apply mul_ne_zero hu.1
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  rw [show (Y j : ℂ)-u = -(u-Y j) by ring, betheF_reverse]
  exact div_ne_zero (hu.2 j).1 (hcross j)

theorem source_argument_not_root {n : ℕ} (Y : Fin n → ℝ) (u : ℂ)
    (hcross : ∀ j, Complex.sinh (u-Y j) ≠ 0) : u ∉ rootSet Y := by
  intro hu
  obtain ⟨j,hj,heq⟩ := Finset.mem_image.mp hu
  exact hcross j (by rw [← heq]; simp)

noncomputable def pathDeterminantAmplitude {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) (H : Finset (Fin n)) (V : Fin n → ℂ) : ℂ :=
  ((-Complex.sinh (Complex.I*lam))^H.card)⁻¹ /
    wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w *
    (((weightedGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y 0 V).submatrix
      (fun i : H => i.val) (fun j : H => j.val)).det /
    ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det *
    (∏ i : H, gaudinEll lam b L Y i.val)

/-- Exact determinant contribution of every replacement endpoint, after
all vacuum bases and Hilbert signs have cancelled. -/
theorem normalizedEndpoint_eq_pathDeterminant {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (hShell : OnShell lam b L Y 0) (hSlavnov : SlavnovIdentity lam b L Y 0)
    (hdet : (gaudinMatrix lam b L Y).det ≠ 0)
    (hpos : ∀ j, 0 < countingSlope lam b L Y (Y j))
    (w : List (RowEntry × ℂ)) (H : Finset (Fin n)) (V R : Fin n → ℂ)
    (hR : Function.Injective R) (hslots : ∀ j, R j = if j ∈ H then V j else (Y j : ℂ))
    (hV : ∀ j ∈ H, SourceRegular lam b L Y (V j))
    (hcross : ∀ j ∈ H, ∀ i, Complex.sinh (V j-Y i) ≠ 0)
    (hC : ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det ≠ 0) :
    normalizedEndpointAmplitude lam b L Y w (Finset.univ.image R) =
      pathDeterminantAmplitude lam b L Y w H V := by
  have hnew : ∀ j ∈ H, V j ∉ rootSet Y := fun j hj => source_argument_not_root Y (V j) (hcross j hj)
  have hbase : ∀ j ∈ H, extractedVacuum lam b L Y (V j) ≠ 0 := fun j hj =>
    source_extractedVacuum_ne_zero lam b L Y (V j) (hV j hj) (hcross j hj)
  have hcancel := replacement_potential_cancel lam h0 hpi b L Y hY H V R hR hslots hnew hbase
  have hfun : R = fun j => if j ∈ H then V j else (Y j : ℂ) := funext hslots
  have hS := deleted_scalar_product lam h0 hpi b L hEven Y hY 0 hShell
    (slavnov_source_of_identity lam b L Y 0 hSlavnov) hdet H V hV hcross hC
  rw [← hfun] at hS
  unfold normalizedEndpointAmplitude
  rw [setScalarProduct_indexed lam h0 hpi b L hEven Y R hR,hS,
    weighted_source_minor lam b L Y 0 hdet hpos H V]
  unfold pathDeterminantAmplitude
  calc
    _ = (vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) (rootSet Y) /
        vacuumPotential (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) (Finset.univ.image R) *
        ((∏ j ∈ H, extractedVacuum lam b L Y (V j))/(∏ j ∈ H, rootVacuumFactor lam b L Y j))) *
      (((-Complex.sinh (Complex.I*lam))^H.card)⁻¹ /
        wordQProduct (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w *
        (((weightedGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y 0 V).submatrix
          (fun i : H => i.val) (fun j : H => j.val)).det /
        ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det *
        (∏ i : H, gaudinEll lam b L Y i.val)) := by ring
    _ = _ := by rw [hcancel,one_mul]

end SixVertex
