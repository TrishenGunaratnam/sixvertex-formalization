import SixVertex.RowAlgebra

namespace SixVertex

set_option maxHeartbeats 1500000

abbrev TripleSpin := Fin 2 × (Fin 2 × Fin 2)

/-- A two-spin matrix acting on the first and second factors. -/
def liftAB (R : Matrix PairSpin PairSpin ℂ) : Matrix TripleSpin TripleSpin ℂ :=
  fun i j => if i.2.2 = j.2.2 then R (i.1,i.2.1) (j.1,j.2.1) else 0

/-- A two-spin matrix acting on the first and third factors. -/
def liftAQ (R : Matrix PairSpin PairSpin ℂ) : Matrix TripleSpin TripleSpin ℂ :=
  fun i j => if i.2.1 = j.2.1 then R (i.1,i.2.2) (j.1,j.2.2) else 0

/-- A two-spin matrix acting on the second and third factors. -/
def liftBQ (R : Matrix PairSpin PairSpin ℂ) : Matrix TripleSpin TripleSpin ℂ :=
  fun i j => if i.1 = j.1 then R (i.2.1,i.2.2) (j.2.1,j.2.2) else 0

/-- Entrywise local RTT: all internal auxiliary and quantum indices are summed.
This is precisely the contraction of the three local matrices on three spins. -/
def LocalRTT (R P Q : Matrix PairSpin PairSpin ℂ) : Prop :=
  ∀ a b c d q r : Fin 2,
    (∑ e : Fin 2, ∑ f : Fin 2, ∑ t : Fin 2,
      R (a,b) (e,f) * P (e,q) (c,t) * Q (f,t) (d,r)) =
    (∑ e : Fin 2, ∑ f : Fin 2, ∑ t : Fin 2,
      Q (b,q) (f,t) * P (a,t) (e,r) * R (e,f) (c,d))

/-- The three scalar relations suffice for every entry of local RTT. -/
theorem sixMatrix_local_RTT (a b ap bp aq bq : ℂ)
    (h1 : a * bp = ap * b + bq)
    (h2 : a * aq = ap + b * bq)
    (h3 : aq * bp = ap * bq + b) :
    LocalRTT (sixMatrix a b 1) (sixMatrix ap bp 1) (sixMatrix aq bq 1) := by
  intro i j k l m n
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    fin_cases l <;> fin_cases m <;> fin_cases n <;>
    simp [sixMatrix, Fin.sum_univ_two] <;>
    first
    | (solve | ring)
    | (solve | linear_combination h1)
    | (solve | linear_combination -h1)
    | (solve | linear_combination h2)
    | (solve | linear_combination -h2)
    | (solve | linear_combination h3)
    | (solve | linear_combination -h3)

/-- The sine addition formula in the determinant form needed by RTT. -/
theorem sine_determinant (l u v : ℂ) :
    Complex.sin (l-u) * Complex.sin v - Complex.sin (l-v) * Complex.sin u =
      Complex.sin l * Complex.sin (v-u) := by
  simp only [Complex.sin_sub]
  ring

/-- The local six-vertex Yang–Baxter relation for the displayed physical R.
Only the nonzero normalization sin(lambda) is assumed. -/
theorem physical_local_RTT (lam : ℝ) (hs : Complex.sin (lam : ℂ) ≠ 0) (u v : ℂ) :
    LocalRTT (physicalR lam (u-v)) (physicalR lam u) (physicalR lam v) := by
  unfold physicalR
  apply sixMatrix_local_RTT
  · have h := sine_determinant lam (u-v) u
    have e : u - (u-v) = v := by ring
    rw [e] at h
    field_simp [hs]
    linear_combination h
  · have h := sine_determinant lam (u-v) (lam-v)
    have e1 : (lam : ℂ) - (lam-v) = v := by ring
    have e2 : ((lam : ℂ)-v) - (u-v) = lam-u := by ring
    rw [e1, e2] at h
    field_simp [hs]
    linear_combination h
  · have h := sine_determinant lam v u
    field_simp [hs]
    linear_combination h

end SixVertex
