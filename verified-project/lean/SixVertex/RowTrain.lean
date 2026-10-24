import SixVertex.RowAlgebra

namespace SixVertex

/-- For fixed quantum input and output, multiply the auxiliary matrices along
the finite chain. This also works for the two-auxiliary-spin space. -/
noncomputable def chainAux {A : Type*} [Fintype A] [DecidableEq A]
    (tiles : ℕ → Fin 2 → Fin 2 → Matrix A A ℂ) :
    (n : ℕ) → RowSpins n → RowSpins n → Matrix A A ℂ
  | 0, _, _ => 1
  | n+1, q, r => tiles 0 q.1 r.1 * chainAux (fun j => tiles (j+1)) n q.2 r.2

/-- The train argument is ordinary matrix associativity; no inverse or
invertibility assumption is needed. -/
theorem chainAux_intertwines {A : Type*} [Fintype A] [DecidableEq A]
    (R : Matrix A A ℂ) (F G : ℕ → Fin 2 → Fin 2 → Matrix A A ℂ)
    (h : ∀ j q r, R * F j q r = G j q r * R)
    (n : ℕ) (q r : RowSpins n) :
    R * chainAux F n q r = chainAux G n q r * R := by
  induction n generalizing F G with
  | zero => simp [chainAux]
  | succ n ih =>
    simp only [chainAux]
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc,
      ih (fun j => F (j+1)) (fun j => G (j+1)) (fun j => h (j+1)),
      ← Matrix.mul_assoc]

def auxiliaryTile (P : Matrix PairSpin PairSpin ℂ) (q r : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ := fun a b => P (a,q) (b,r)

theorem rowBlock_eq_chainAux (P : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (a b : Fin 2) (q r : RowSpins n) :
    rowBlock P n a b q r = chainAux (fun j => auxiliaryTile (P j)) n q r a b := by
  induction n generalizing P a b with
  | zero => simp [rowBlock, chainAux, Matrix.one_apply]
  | succ n ih =>
    simp only [rowBlock, chainAux, Matrix.mul_apply, auxiliaryTile]
    apply Finset.sum_congr rfl
    intro c hc
    rw [ih]

/-- At each site the P row acts after the Q row. -/
noncomputable def forwardTile (P Q : Matrix PairSpin PairSpin ℂ) (q r : Fin 2) :
    Matrix PairSpin PairSpin ℂ := fun a b =>
  ∑ t : Fin 2, P (a.1,q) (b.1,t) * Q (a.2,t) (b.2,r)

/-- The two row actions in the opposite order. -/
noncomputable def reverseTile (P Q : Matrix PairSpin PairSpin ℂ) (q r : Fin 2) :
    Matrix PairSpin PairSpin ℂ := fun a b =>
  ∑ t : Fin 2, Q (a.2,q) (b.2,t) * P (a.1,t) (b.1,r)

theorem sum_four_permute {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] (f : A → B → C → D → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = (∑ c, ∑ d, ∑ a, ∑ b, f a b c d) := by
  calc
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := by rw [Finset.sum_comm]
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      calc
        _ = ∑ a, ∑ d, ∑ b, f a b c d := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

/-- Expanding the product of two whole rows is equivalent to contracting
their two local tiles at each site. This proves the tensor-factor reordering
used by the train argument, rather than assuming it. -/
theorem forward_chain_eq_product (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (a b c d : Fin 2) (q r : RowSpins n) :
    chainAux (fun j => forwardTile (P j) (Q j)) n q r (a,b) (c,d) =
      (rowBlock P n a c * rowBlock Q n b d) q r := by
  induction n generalizing P Q a b c d with
  | zero =>
    simp only [chainAux, Matrix.one_apply, Prod.mk.injEq,
      rowBlock]
    change (if a = c ∧ b = d then (1 : ℂ) else 0) =
      ∑ _ : Unit, (if a = c then (1 : ℂ) else 0) * (if b = d then 1 else 0)
    by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1,h2]
  | succ n ih =>
    rw [Matrix.mul_apply]
    change _ = ∑ s : Fin 2 × RowSpins n,
      rowBlock P (n+1) a c q s * rowBlock Q (n+1) b d s r
    rw [Fintype.sum_prod_type]
    simp only [chainAux, Matrix.mul_apply, Fintype.sum_prod_type, forwardTile]
    simp_rw [ih, Matrix.mul_apply]
    simp only [rowBlock]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [sum_four_permute]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro f hf
    ring

theorem chainAux_submatrix {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : B ≃ A)
    (P : ℕ → Fin 2 → Fin 2 → Matrix A A ℂ)
    (n : ℕ) (q r : RowSpins n) :
    chainAux (fun j q r => (P j q r).submatrix e e) n q r =
      (chainAux P n q r).submatrix e e := by
  induction n generalizing P with
  | zero => simp [chainAux, Matrix.submatrix_one_equiv]
  | succ n ih =>
    simp only [chainAux, ih]
    rw [Matrix.submatrix_mul_equiv]

theorem reverse_chain_eq_product (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (a b c d : Fin 2) (q r : RowSpins n) :
    chainAux (fun j => reverseTile (P j) (Q j)) n q r (a,b) (c,d) =
      (rowBlock Q n b d * rowBlock P n a c) q r := by
  change chainAux
    (fun j q r => (forwardTile (Q j) (P j) q r).submatrix
      (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.prodComm (Fin 2) (Fin 2)))
      n q r (a,b) (c,d) = _
  rw [chainAux_submatrix]
  exact forward_chain_eq_product Q P n b a d c q r

noncomputable def forwardRows (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (q r : RowSpins n) : Matrix PairSpin PairSpin ℂ := fun a b =>
  (rowBlock P n a.1 b.1 * rowBlock Q n a.2 b.2) q r

noncomputable def reverseRows (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (q r : RowSpins n) : Matrix PairSpin PairSpin ℂ := fun a b =>
  (rowBlock Q n a.2 b.2 * rowBlock P n a.1 b.1) q r

theorem forwardRows_eq_chainAux (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (q r : RowSpins n) :
    forwardRows P Q n q r = chainAux (fun j => forwardTile (P j) (Q j)) n q r := by
  ext ⟨a,b⟩ ⟨c,d⟩
  exact (forward_chain_eq_product P Q n a b c d q r).symm

theorem reverseRows_eq_chainAux (P Q : ℕ → Matrix PairSpin PairSpin ℂ)
    (n : ℕ) (q r : RowSpins n) :
    reverseRows P Q n q r = chainAux (fun j => reverseTile (P j) (Q j)) n q r := by
  ext ⟨a,b⟩ ⟨c,d⟩
  exact (reverse_chain_eq_product P Q n a b c d q r).symm

end SixVertex
