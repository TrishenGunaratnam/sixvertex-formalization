import SixVertex.HilbertAdjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace SixVertex
open scoped ComplexConjugate Matrix

/-- The spin Hilbert space uses the L2 norm, not the sup norm on a raw Pi type. -/
abbrev SpinHilbert (L : ℕ) := EuclideanSpace ℂ (RowSpins L)

noncomputable def creationList (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (U : List ℂ) :
    Matrix (RowSpins L) (RowSpins L) ℂ :=
  (U.map (betheB (Complex.I*lam) (fun j => (b j : ℂ)) L)).prod

noncomputable def annihilationList (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : List ℝ) :
    Matrix (RowSpins L) (RowSpins L) ℂ :=
  (Y.map (fun y : ℝ => betheC (Complex.I*lam) (fun j => (b j : ℂ)) L (y : ℂ))).prod

noncomputable def physicalListVector (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (U : List ℂ) : SpinHilbert L :=
  WithLp.toLp 2 (fun q => (quantumGauge L * creationList lam b L U) q (plusSpins L))

noncomputable def physicalBetheVector {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : SpinHilbert L :=
  physicalListVector lam b L ((List.finRange n).map (fun j => (Y j : ℂ)))

noncomputable def algebraicListScalarProduct (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : List ℝ) (U : List ℂ) : ℂ :=
  (annihilationList lam b L Y * creationList lam b L U) (plusSpins L) (plusSpins L)

theorem bethe_CC (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (x y : ℂ) :
    Commute (betheC (Complex.I*lam) (fun j => (b j : ℂ)) L x)
      (betheC (Complex.I*lam) (fun j => (b j : ℂ)) L y) := by
  have h := congrArg Matrix.conjTranspose
    (bethe_BB (Complex.I*lam) (physical_deformation_ne_zero lam h0 hpi)
      (fun j => (b j : ℂ)) L (conj x) (conj y)).eq
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    betheB_hilbert_adjoint lam b L hEven, betheB_hilbert_adjoint lam b L hEven] at h
  change _ * _ = _ * _
  simpa only [Complex.conj_conj, neg_mul_neg] using h.symm

/-- The adjoint of an arbitrary real-root creation list. No on-shell or
root-separation assumption is needed for this Hilbert-space identity. -/
theorem creationList_adjoint_real (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : List ℝ) :
    (creationList lam b L (Y.map Complex.ofReal))ᴴ =
      (-1 : ℂ)^Y.length • annihilationList lam b L Y := by
  induction Y with
  | nil => simp [creationList, annihilationList]
  | cons y Y ih =>
    have hc : Commute (betheC (Complex.I*lam) (fun j => (b j : ℂ)) L y)
        (annihilationList lam b L Y) := by
      apply Commute.list_prod_right
      intro M hM
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hM
      exact bethe_CC lam h0 hpi b L hEven y z
    change (betheB (Complex.I*lam) (fun j => (b j : ℂ)) L y *
      creationList lam b L (Y.map Complex.ofReal))ᴴ = _
    rw [Matrix.conjTranspose_mul, ih, betheB_hilbert_adjoint lam b L hEven]
    simp only [Complex.conj_ofReal, annihilationList, List.map_cons, List.prod_cons,
      List.length_cons, pow_succ] at hc ⊢
    rw [smul_mul_assoc, mul_neg, hc.symm.eq]
    simp [mul_smul, smul_neg]

theorem parity_signs_conj (L : ℕ) (q : RowSpins L) :
    conj (evenSign L q) = evenSign L q ∧ conj (oddSign L q) = oddSign L q := by
  induction L with
  | zero => simp [evenSign, oddSign]
  | succ L ih =>
    have hz : conj (zSpin q.1) = zSpin q.1 := by
      rcases q with ⟨a, q⟩
      fin_cases a <;> simp [zSpin]
    simp only [evenSign, oddSign, map_mul, hz, (ih q.2).1, (ih q.2).2, and_self]

/-- The physical gauge preserves the Hilbert inner product, entry by entry. -/
theorem physicalListVector_inner (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (U V : List ℂ) :
    inner ℂ (physicalListVector lam b L U) (physicalListVector lam b L V) =
      ∑ q, (creationList lam b L V) q (plusSpins L) * conj ((creationList lam b L U) q (plusSpins L)) := by
  rw [physicalListVector, physicalListVector, EuclideanSpace.inner_toLp_toLp]
  simp only [quantumGauge, Matrix.diagonal_mul, dotProduct, Pi.star_apply, Complex.star_def,
    map_mul, (parity_signs_conj L _).1]
  apply Finset.sum_congr rfl
  intro q hq
  linear_combination
    ((creationList lam b L V) q (plusSpins L) * conj ((creationList lam b L U) q (plusSpins L))) *
      (parity_signs_square L q).1

/-- Hilbert duality for arbitrary off-shell right lists, including repeated
complex arguments. This identity itself is independent of Slavnov. -/
theorem physical_inner_algebraic_list (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : List ℝ) (U : List ℂ) :
    inner ℂ (physicalListVector lam b L (Y.map Complex.ofReal)) (physicalListVector lam b L U) =
      (-1 : ℂ)^Y.length * algebraicListScalarProduct lam b L Y U := by
  rw [physicalListVector_inner]
  have hd := creationList_adjoint_real lam h0 hpi b L hEven Y
  have he (q : RowSpins L) : conj ((creationList lam b L (Y.map Complex.ofReal)) q (plusSpins L)) =
      (-1 : ℂ)^Y.length * (annihilationList lam b L Y) (plusSpins L) q := by
    exact congrArg (fun M => M (plusSpins L) q) hd
  simp only [he, algebraicListScalarProduct, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem algebraicListScalarProduct_eq {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (U : Fin n → ℂ) :
    algebraicListScalarProduct lam b L ((List.finRange n).map Y) ((List.finRange n).map U) =
      algebraicScalarProduct lam b L Y U := by
  simp only [algebraicListScalarProduct, annihilationList, creationList, List.map_map,
    Function.comp_def, algebraicScalarProduct, betheListState]
  rw [← Matrix.mul_assoc, mul_vacuumProjector]
  simp only [ite_true]

/-- The exact bridge from the manuscript's S(Y,U) to the spin Hilbert product. -/
theorem physical_inner_algebraic {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (hEven : Even L) (Y : Fin n → ℝ) (U : Fin n → ℂ) :
    inner ℂ (physicalBetheVector lam b L Y)
      (physicalListVector lam b L ((List.finRange n).map U)) =
      (-1 : ℂ)^n * algebraicScalarProduct lam b L Y U := by
  have h := physical_inner_algebraic_list lam h0 hpi b L hEven ((List.finRange n).map Y)
    ((List.finRange n).map U)
  simpa only [physicalBetheVector, List.map_map, Function.comp_def, List.length_map,
    List.length_finRange, algebraicListScalarProduct_eq] using h

end SixVertex
