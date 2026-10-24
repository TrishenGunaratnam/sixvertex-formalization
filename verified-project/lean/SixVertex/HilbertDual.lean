import SixVertex.BetheHilbertSpace

namespace SixVertex
open scoped ComplexConjugate Matrix

noncomputable def normalizeSpinVector {L : ℕ} (v : SpinHilbert L) : SpinHilbert L :=
  ((‖v‖⁻¹ : ℝ) : ℂ) • v

noncomputable def physicalUnitBetheVector {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : SpinHilbert L := normalizeSpinVector (physicalBetheVector lam b L Y)

theorem physical_bethe_inner {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y Z : Fin n → ℝ) :
    inner ℂ (physicalBetheVector lam b L Y) (physicalBetheVector lam b L Z) =
      (-1 : ℂ)^n * algebraicScalarProduct lam b L Y (fun k => (Z k : ℂ)) :=
  physical_inner_algebraic lam h0 hpi b L hEven Y (fun k => (Z k : ℂ))

/-- The norm identity is unconditional on Slavnov, even for off-shell or
repeated real roots. Nonvanishing is handled separately below. -/
theorem physical_bethe_norm_sq {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) :
    ((‖physicalBetheVector lam b L Y‖^2 : ℝ) : ℂ) =
      (-1 : ℂ)^n * algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) := by
  calc
    ((‖physicalBetheVector lam b L Y‖^2 : ℝ) : ℂ) = (‖physicalBetheVector lam b L Y‖ : ℂ)^2 := Complex.ofReal_pow _ _
    _ = inner ℂ (physicalBetheVector lam b L Y) (physicalBetheVector lam b L Y) := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (physicalBetheVector lam b L Y)).symm
    _ = _ := physical_bethe_inner lam h0 hpi b L hEven Y Y

theorem physical_bethe_ne_zero {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist) (hSlavnov : SlavnovIdentity lam b L Y twist)
    (hdet : (gaudinMatrix lam b L Y).det ≠ 0) : physicalBetheVector lam b L Y ≠ 0 := by
  have hS := gaudin_norm_ne_zero lam h0 hpi b L hEven Y hY twist hShell
    (slavnov_source_of_identity lam b L Y twist hSlavnov) hdet
  have h := physical_bethe_inner lam h0 hpi b L hEven Y Y
  intro hz
  rw [hz, inner_zero_left] at h
  exact (mul_ne_zero (pow_ne_zero n (by norm_num)) hS) h.symm

theorem physical_bethe_norm_pos {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (twist : ℝ) (hShell : OnShell lam b L Y twist) (hSlavnov : SlavnovIdentity lam b L Y twist)
    (hdet : (gaudinMatrix lam b L Y).det ≠ 0) :
    0 < ‖physicalBetheVector lam b L Y‖^2 := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (physical_bethe_ne_zero lam h0 hpi b L hEven Y hY twist hShell hSlavnov hdet))

theorem normalizeSpinVector_norm {L : ℕ} (v : SpinHilbert L) (hv : v ≠ 0) :
    ‖normalizeSpinVector v‖ = 1 := by
  rw [normalizeSpinVector, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem normalized_spin_overlap {L : ℕ} (u v : SpinHilbert L) (hu : u ≠ 0) (hv : v ≠ 0) :
    ((‖inner ℂ (normalizeSpinVector u) (normalizeSpinVector v)‖^2 : ℝ) : ℂ) =
      inner ℂ u v * inner ℂ v u / (inner ℂ u u * inner ℂ v v) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [normalizeSpinVector, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, map_mul, map_inv₀, Complex.conj_conj, inner_conj_symm, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_inv]
  have hnu : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have hnv : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  field_simp [hnu, hnv]
  <;> first | ac_rfl | ring

/-- The normalized overlap identity follows from Hilbert duality and positivity.
The two twists may differ. Its only external input is Slavnov for each root list. -/
theorem physical_bethe_overlap {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y Z : Fin n → ℝ)
    (hY : Function.Injective Y) (hZ : Function.Injective Z) (tY tZ : ℝ)
    (hShellY : OnShell lam b L Y tY) (hShellZ : OnShell lam b L Z tZ)
    (hSlavnovY : SlavnovIdentity lam b L Y tY) (hSlavnovZ : SlavnovIdentity lam b L Z tZ)
    (hdetY : (gaudinMatrix lam b L Y).det ≠ 0) (hdetZ : (gaudinMatrix lam b L Z).det ≠ 0) :
    ((‖inner ℂ (physicalUnitBetheVector lam b L Y) (physicalUnitBetheVector lam b L Z)‖^2 : ℝ) : ℂ) =
      algebraicScalarProduct lam b L Y (fun k => (Z k : ℂ)) *
      algebraicScalarProduct lam b L Z (fun k => (Y k : ℂ)) /
      (algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) *
        algebraicScalarProduct lam b L Z (fun k => (Z k : ℂ))) := by
  have hny := physical_bethe_ne_zero lam h0 hpi b L hEven Y hY tY hShellY hSlavnovY hdetY
  have hnz := physical_bethe_ne_zero lam h0 hpi b L hEven Z hZ tZ hShellZ hSlavnovZ hdetZ
  rw [physicalUnitBetheVector, physicalUnitBetheVector, normalized_spin_overlap _ _ hny hnz,
    physical_bethe_inner lam h0 hpi b L hEven Y Z,
    physical_bethe_inner lam h0 hpi b L hEven Z Y,
    physical_bethe_inner lam h0 hpi b L hEven Y Y,
    physical_bethe_inner lam h0 hpi b L hEven Z Z]
  have hs : (-1 : ℂ)^n * (-1)^n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℂ)^n * (-1)^n) *
        (algebraicScalarProduct lam b L Y (fun k => (Z k : ℂ)) * algebraicScalarProduct lam b L Z (fun k => (Y k : ℂ))) /
        (((-1 : ℂ)^n * (-1)^n) *
          (algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) * algebraicScalarProduct lam b L Z (fun k => (Z k : ℂ)))) := by ring
    _ = _ := by rw [hs, one_mul, one_mul]

/-- Lemma 2.5: the operator identity, exact positive Hilbert norm, normalized
physical state and two-orientation overlap. Real staggered sites are included. -/
structure HilbertDual (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) : Prop where
  adjoint : ∀ x : ℂ, (betheB (Complex.I*lam) (fun j => (b j : ℂ)) L x)ᴴ =
    -betheC (Complex.I*lam) (fun j => (b j : ℂ)) L (conj x)
  norm_identity : ∀ (n : ℕ) (Y : Fin n → ℝ),
    ((‖physicalBetheVector lam b L Y‖^2 : ℝ) : ℂ) =
      (-1 : ℂ)^n * algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ))
  positive_unit : ∀ (n : ℕ) (Y : Fin n → ℝ) (t : ℝ), Function.Injective Y →
    OnShell lam b L Y t → SlavnovIdentity lam b L Y t → (gaudinMatrix lam b L Y).det ≠ 0 →
    0 < ‖physicalBetheVector lam b L Y‖^2 ∧ ‖physicalUnitBetheVector lam b L Y‖ = 1
  overlap : ∀ (n : ℕ) (Y Z : Fin n → ℝ) (tY tZ : ℝ), Function.Injective Y → Function.Injective Z →
    OnShell lam b L Y tY → OnShell lam b L Z tZ →
    SlavnovIdentity lam b L Y tY → SlavnovIdentity lam b L Z tZ →
    (gaudinMatrix lam b L Y).det ≠ 0 → (gaudinMatrix lam b L Z).det ≠ 0 →
    ((‖inner ℂ (physicalUnitBetheVector lam b L Y) (physicalUnitBetheVector lam b L Z)‖^2 : ℝ) : ℂ) =
      algebraicScalarProduct lam b L Y (fun k => (Z k : ℂ)) * algebraicScalarProduct lam b L Z (fun k => (Y k : ℂ)) /
      (algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) * algebraicScalarProduct lam b L Z (fun k => (Z k : ℂ)))

theorem hilbert_dual (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hL : 4 ≤ L) (hEven : Even L) : HilbertDual lam b L := by
  refine ⟨betheB_hilbert_adjoint lam b L hEven, ?_, ?_, ?_⟩
  · exact fun n Y => physical_bethe_norm_sq lam h0 hpi b L hEven Y
  · intro n Y t hY hShell hSlavnov hdet
    exact ⟨physical_bethe_norm_pos lam h0 hpi b L hEven Y hY t hShell hSlavnov hdet,
      normalizeSpinVector_norm _ (physical_bethe_ne_zero lam h0 hpi b L hEven Y hY t hShell hSlavnov hdet)⟩
  · intro n Y Z tY tZ hY hZ hSY hSZ hSlY hSlZ hdY hdZ
    exact physical_bethe_overlap lam h0 hpi b L hEven Y Z hY hZ tY tZ hSY hSZ hSlY hSlZ hdY hdZ

end SixVertex
