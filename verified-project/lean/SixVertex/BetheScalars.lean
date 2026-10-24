import SixVertex.FiniteRTT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.NoncommRing

/-!
# Scalar functions for Section 2, Single-entry actions

The deformation parameter `t` is ultimately `i * lambda`. Keeping it complex
here makes the algebraic identities independent of the physical real slice.
All division hypotheses remain explicit. The named action lemma is assembled
in SingleEntryActions.lean.
-/

namespace SixVertex

noncomputable def betheF (t z : ℂ) : ℂ := Complex.sinh (z+t) / Complex.sinh z
noncomputable def betheG (t z : ℂ) : ℂ := Complex.sinh t / Complex.sinh z
noncomputable def betheBeta (t z : ℂ) : ℂ := Complex.sinh t / Complex.sinh (z+t)

theorem sinh_determinant (t u v : ℂ) :
    Complex.sinh (u+t) * Complex.sinh v - Complex.sinh (v+t) * Complex.sinh u =
      Complex.sinh t * Complex.sinh (v-u) := by
  simp only [Complex.sinh_add, Complex.sinh_sub]
  ring

@[simp] theorem betheBeta_zero (t : ℂ) (ht : Complex.sinh t ≠ 0) :
    betheBeta t 0 = 1 := by simp [betheBeta, ht]

theorem betheG_neg (t z : ℂ) : betheG t (-z) = -betheG t z := by
  simp [betheG, Complex.sinh_neg, div_neg]

theorem betheBeta_mul_f (t z : ℂ) (h : Complex.sinh (z+t) ≠ 0) :
    betheBeta t z * betheF t z = betheG t z := by
  unfold betheBeta betheF betheG
  field_simp

noncomputable def hyperbolicR (t u : ℂ) : Matrix PairSpin PairSpin ℂ :=
  sixMatrix (Complex.sinh (u+t) / Complex.sinh t) (Complex.sinh u / Complex.sinh t) 1

theorem hyperbolic_local_RTT (t : ℂ) (ht : Complex.sinh t ≠ 0) (u v : ℂ) :
    LocalRTT (hyperbolicR t (u-v)) (hyperbolicR t u) (hyperbolicR t v) := by
  unfold hyperbolicR
  apply sixMatrix_local_RTT
  · have h := sinh_determinant t (u-v) u
    have e : u - (u-v) = v := by ring
    rw [e] at h
    field_simp [ht]
    linear_combination h
  · have h := sinh_determinant t (u-v) (-(v+t))
    have e1 : -(v+t)+t = -v := by ring
    have e2 : -(v+t)-(u-v) = -(u+t) := by ring
    rw [e1, e2, Complex.sinh_neg, Complex.sinh_neg, Complex.sinh_neg] at h
    field_simp [ht]
    linear_combination -h
  · have h := sinh_determinant t v u
    field_simp [ht]
    linear_combination h

/-- The elementary coefficient identity used in the diagonal-action induction. -/
theorem bethe_diagonal_cocycle (t v u p : ℂ)
    (hvu : Complex.sinh (v-u) ≠ 0) (hvp : Complex.sinh (v-p) ≠ 0)
    (hup : Complex.sinh (u-p) ≠ 0) :
    betheF t (u-v) * betheG t (v-p) + betheG t (v-u) * betheG t (u-p) =
      betheG t (v-p) * betheF t (u-p) := by
  have h := sinh_determinant t (u-v) (u-p)
  have e : (u-p)-(u-v) = v-p := by ring
  rw [e] at h
  have hn : Complex.sinh (u-v) = -Complex.sinh (v-u) := by
    rw [show u-v = -(v-u) by ring, Complex.sinh_neg]
  rw [hn] at h
  unfold betheF betheG
  rw [hn]
  field_simp [hvu, hvp, hup]
  linear_combination -(Complex.sinh t) * h

theorem bethe_lower_cocycle (t v u p : ℂ)
    (huv : Complex.sinh (u-v) ≠ 0) (hpv : Complex.sinh (p-v) ≠ 0)
    (hpu : Complex.sinh (p-u) ≠ 0) :
    betheF t (v-u) * betheG t (p-v) + betheG t (u-v) * betheG t (p-u) =
      betheG t (p-v) * betheF t (p-u) := by
  have e1 : -v - -u = u-v := by ring
  have e2 : -v - -p = p-v := by ring
  have e3 : -u - -p = p-u := by ring
  have h := bethe_diagonal_cocycle t (-v) (-u) (-p)
    (by rwa [e1]) (by rwa [e2]) (by rwa [e3])
  have e4 : -u - -v = v-u := by ring
  have e5 : -p - -u = u-p := by ring
  simpa only [e1, e2, e3, e4, e5] using h

/-- Regularity domain for the displayed generic action formulas. Shifted
sinh denominators are retained even when a subsequent cancellation removes them. -/
def BetheRegular (t : ℂ) (S : Finset ℂ) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → Complex.sinh (x-y) ≠ 0) ∧
  (∀ x ∈ S, ∀ y ∈ S, Complex.sinh (x-y+t) ≠ 0)

theorem BetheRegular.mono {t : ℂ} {S T : Finset ℂ}
    (h : BetheRegular t S) (hTS : T ⊆ S) : BetheRegular t T := by
  exact ⟨fun x hx y hy hn => h.1 x (hTS hx) y (hTS hy) hn,
    fun x hx y hy => h.2 x (hTS hx) y (hTS hy)⟩

end SixVertex
