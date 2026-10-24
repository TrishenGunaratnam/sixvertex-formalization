import SixVertex.PhysicalLinkOperator

namespace SixVertex
noncomputable section

/-- Product-rule derivative of the existing ordered row contraction.
It differentiates each physical tile,with the original contraction
order and both auxiliary boundary spins preserved. -/
def rowBlockDifferential (A B : ℕ → Matrix PairSpin PairSpin ℂ) :
    (n : ℕ) → Fin 2 → Fin 2 → Matrix (RowSpins n) (RowSpins n) ℂ
  | 0,_,_ => 0
  | n+1,a,b => fun q r => ∑ c : Fin 2,
      (B 0 (a,q.1) (c,r.1)*rowBlock (fun j => A (j+1)) n c b q.2 r.2+
      A 0 (a,q.1) (c,r.1)*rowBlockDifferential (fun j => A (j+1)) (fun j => B (j+1)) n c b q.2 r.2)

/-- Genuine derivative of every finite existing row block,not an assumed
tile-insertion rule. -/
theorem rowBlock_hasDerivAt (P : ℕ → ℂ → Matrix PairSpin PairSpin ℂ)
    (B : ℕ → Matrix PairSpin PairSpin ℂ) (z₀ : ℂ)
    (hP : ∀ j,HasDerivAt (P j) (B j) z₀) (n : ℕ) (a b : Fin 2) :
    HasDerivAt (fun z => rowBlock (fun j => P j z) n a b)
      (rowBlockDifferential (fun j => P j z₀) B n a b) z₀ := by
  induction n generalizing P B a b with
  | zero =>
      apply hasDerivAt_pi.mpr
      intro q
      apply hasDerivAt_pi.mpr
      intro r
      exact hasDerivAt_const z₀ (if a=b then (1 : ℂ) else 0)
  | succ n ih =>
      apply hasDerivAt_pi.mpr
      intro q
      apply hasDerivAt_pi.mpr
      intro r
      change HasDerivAt (fun z => ∑ c : Fin 2,
        P 0 z (a,q.1) (c,r.1)*rowBlock (fun j => P (j+1) z) n c b q.2 r.2)
        (∑ c : Fin 2,(B 0 (a,q.1) (c,r.1)*rowBlock (fun j => P (j+1) z₀) n c b q.2 r.2+
          P 0 z₀ (a,q.1) (c,r.1)*rowBlockDifferential (fun j => P (j+1) z₀) (fun j => B (j+1)) n c b q.2 r.2)) z₀
      apply HasDerivAt.fun_sum
      intro c _
      have hp := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hP 0) (a,q.1)) (c,r.1)
      have ht := ih (fun j => P (j+1)) (fun j => B (j+1)) (fun j => hP (j+1)) c b
      have hr := hasDerivAt_pi.mp (hasDerivAt_pi.mp ht q.2) r.2
      exact hp.mul hr

/-- Derivative of the existing marked auxiliary trace. -/
def markedRowDifferential (A B : ℕ → Matrix PairSpin PairSpin ℂ) (n : ℕ)
    (D : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (RowSpins n) (RowSpins n) ℂ :=
  ∑ a : Fin 2,∑ b : Fin 2,D b a • rowBlockDifferential A B n a b

theorem markedRow_hasDerivAt (P : ℕ → ℂ → Matrix PairSpin PairSpin ℂ)
    (B : ℕ → Matrix PairSpin PairSpin ℂ) (z₀ : ℂ)
    (hP : ∀ j,HasDerivAt (P j) (B j) z₀) (n : ℕ)
    (D : Matrix (Fin 2) (Fin 2) ℂ) :
    HasDerivAt (fun z => markedRow (fun j => P j z) n D)
      (markedRowDifferential (fun j => P j z₀) B n D) z₀ := by
  apply hasDerivAt_pi.mpr
  intro q
  apply hasDerivAt_pi.mpr
  intro r
  simp only [markedRow,markedRowDifferential,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp (rowBlock_hasDerivAt P B z₀ hP n a b) q) r
  exact h.const_mul (D b a)

/-- The actual homogeneous physical transfer row,in its physical local
spectral coordinate. -/
def homogeneousPhysicalRow (lam : ℝ) (L : ℕ) (z : ℂ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  markedRow (fun _ => physicalR lam z) L 1

def homogeneousPhysicalRowPrimeZero (lam : ℝ) (L : ℕ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  markedRowDifferential (fun _ => swapTile) (fun _ => physicalRPrimeZero lam) L 1

/-- The derivative of the actual full homogeneous row at its swap point. -/
theorem homogeneousPhysicalRow_hasDerivAt_zero (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (L : ℕ) :
    HasDerivAt (homogeneousPhysicalRow lam L) (homogeneousPhysicalRowPrimeZero lam L) (0 : ℂ) := by
  have hs : Complex.sin (lam : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have h := markedRow_hasDerivAt (fun _ => physicalR lam) (fun _ => physicalRPrimeZero lam) 0
    (fun _ => physicalR_hasDerivAt_zero lam) L 1
  change HasDerivAt (fun z => markedRow (fun _ => physicalR lam z) L 1)
    (markedRowDifferential (fun _ => swapTile) (fun _ => physicalRPrimeZero lam) L 1) 0
  simpa only [physicalR_at_zero lam hs] using h

theorem homogeneousPhysicalRow_at_zero (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (n : ℕ) :
    homogeneousPhysicalRow lam (n+1) 0=spinPermutation (cyclicSpinTranslation n) := by
  have hs : Complex.sin (lam : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  simpa only [homogeneousPhysicalRow,physicalR_at_zero lam hs] using markedRow_swaps n

/-- The actual right logarithmic row derivative,using the explicit
inverse cyclic translation at the swap point. -/
def homogeneousLinkHamiltonian (lam eta : ℝ) (n : ℕ) :
    Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ :=
  (-(eta : ℂ)) • (homogeneousPhysicalRowPrimeZero lam (n+1)*spinPermutation (cyclicSpinTranslation n).symm)

theorem homogeneousLinkHamiltonian_apply_eq_row_derivative (lam eta : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (n : ℕ) (q r : RowSpins (n+1)) :
    homogeneousLinkHamiltonian lam eta n q r=
      (-(eta : ℂ))*(∑ t : RowSpins (n+1),
        deriv (fun z => homogeneousPhysicalRow lam (n+1) z q t) (0 : ℂ)*
          spinPermutation (cyclicSpinTranslation n).symm t r) := by
  simp only [homogeneousLinkHamiltonian,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (homogeneousPhysicalRow_hasDerivAt_zero lam h0 hpi (n+1)) q) t
  rw [h.deriv]

end
end SixVertex
