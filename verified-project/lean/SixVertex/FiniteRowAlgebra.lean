import SixVertex.RowGauge
import SixVertex.RowCommutation
import SixVertex.RowEndpoints

/-!
# The named lemma `lem:row-algebra`: Finite row algebra

This is the complete statement from Section 2, in the spin basis used by
the manuscript. The chain length is even and at least four, as specified
in Section 1, line 16. The local parameter satisfies 0 < lambda < pi.

`monodromy` contracts every internal auxiliary spin in the ordered product
of the displayed local matrices. `markedRow` is tr_a(D M). The usual
operator adjoint in this orthonormal basis is `Matrix.conjTranspose`.

The RTT equality is written for every quantum input/output pair, as a
four-by-four auxiliary matrix equality. `forwardRows` and `reverseRows`
retain the quantum matrix products in the indicated order. Thus this is
the full operator identity, not merely a vacuum expectation.

Every clause is proved from the explicit matrices; no Bethe-vector,
infinite-volume, convergence or estimate assumption is used.
-/

namespace SixVertex

open scoped ComplexConjugate Matrix

structure FiniteRowAlgebra (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) : Prop where
  gauge : ∀ x : ℂ,
    monodromy (fun j => physicalTile lam (b j) x) L =
      parityP L * monodromy (fun j => standardL lam (x-b j)) L * parityP L * parityQ L
  adjoint : ∀ (x : ℂ) (D : Matrix (Fin 2) (Fin 2) ℂ),
    (markedRow (fun j => physicalTile lam (b j) x) L D)ᴴ =
      markedRow (fun j => physicalTile lam (b j) (conj x)) L (spinX * D.map conj * spinX)
  commute : ∀ (p s : ℂ) (d : Fin 2 → ℂ),
    markedRow (fun j => physicalTile lam (b j) p) L (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) s) L (Matrix.diagonal d) =
      markedRow (fun j => physicalTile lam (b j) s) L (Matrix.diagonal d) *
        markedRow (fun j => physicalTile lam (b j) p) L (Matrix.diagonal d)
  rtt : ∀ (p s : ℂ) (q r : RowSpins L),
    physicalIntertwiner lam (p-s) *
        forwardRows (fun j => physicalTile lam (b j) p)
          (fun j => physicalTile lam (b j) s) L q r =
      reverseRows (fun j => physicalTile lam (b j) p)
        (fun j => physicalTile lam (b j) s) L q r * physicalIntertwiner lam (p-s)
  exchange : ∀ (p s : ℂ) (R : (Matrix PairSpin PairSpin ℂ)ˣ),
    (R : Matrix PairSpin PairSpin ℂ) = physicalIntertwiner lam (p-s) →
    ∀ (D : Matrix PairSpin PairSpin ℂ) (q r : RowSpins L),
      jointMarkedRow D (forwardRows (fun j => physicalTile lam (b j) p)
          (fun j => physicalTile lam (b j) s) L q r) =
        jointMarkedRow ((R : Matrix PairSpin PairSpin ℂ) * D * (↑R⁻¹ : Matrix PairSpin PairSpin ℂ))
          (reverseRows (fun j => physicalTile lam (b j) p)
            (fun j => physicalTile lam (b j) s) L q r)
  translation :
    markedRow (fun _ => physicalTile lam 0 (Complex.I * lam / 2)) L 1 =
      spinPermutation (cyclicTranslation L)
  inverse_translation :
    markedRow (fun _ => physicalTile lam 0 (-Complex.I * lam / 2)) L 1 =
      spinPermutation (cyclicTranslation L).symm

/-- Section 2, `lem:row-algebra`, including all its clauses. -/
theorem finite_row_algebra (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (L : ℕ) (hL : 4 ≤ L) (hEven : Even L) (b : ℕ → ℝ) :
    FiniteRowAlgebra lam b L := by
  have hs : Complex.sin (lam : ℂ) ≠ 0 := by
    have h : (Real.sin lam : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
    simpa only [Complex.ofReal_sin] using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨k,hk⟩ := hEven
    have he : L = 2*k := by omega
    clear hk
    subst L
    exact physical_monodromy_gauge lam b x k
  · exact fun x D => physical_markedRow_adjoint lam b x L D
  · exact fun p s d => physical_diagonal_rows_commute lam hs b p s L d
  · exact fun p s q r => physical_finite_chain_RTT lam hs b p s L q r
  · intro p s R hR D q r
    apply joint_mark_exchange R D
    rw [hR]
    exact physical_finite_chain_RTT lam hs b p s L q r
  · cases L with
    | zero => omega
    | succ n => exact physical_endpoint_translation lam hs n
  · cases L with
    | zero => omega
    | succ n => exact physical_endpoint_inverse lam hs n

end SixVertex
