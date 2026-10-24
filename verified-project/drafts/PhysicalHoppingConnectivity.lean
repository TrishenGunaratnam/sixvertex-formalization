import SixVertex.PhysicalHamiltonianSector
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SixVertex
noncomputable section

/-- The concrete adjacent swap,with the position of its left site kept
so that rotating away a leading site decreases that position. -/
inductive AdjacentSpinSwapAt : (L k : ℕ) → RowSpins L → RowSpins L → Prop
  | head (L : ℕ) (a b : Fin 2) (t : RowSpins L) (h : a≠b) :
      AdjacentSpinSwapAt (L+2) 0 (a,b,t) (b,a,t)
  | tail (L k : ℕ) (a : Fin 2) {q r : RowSpins L} (h : AdjacentSpinSwapAt L k q r) :
      AdjacentSpinSwapAt (L+1) (k+1) (a,q) (a,r)

theorem adjacentSpinSwap_exists_at {L : ℕ} {q r : RowSpins L}
    (h : AdjacentSpinSwap L q r) : ∃ k,AdjacentSpinSwapAt L k q r := by
  induction h with
  | head L a b t h => exact ⟨0,.head L a b t h⟩
  | tail L a h ih =>
    obtain ⟨k,hk⟩ := ih
    exact ⟨k+1,.tail L k a hk⟩

theorem adjacentSpinSwapAt_append {L k : ℕ} {q r : RowSpins L}
    (h : AdjacentSpinSwapAt L k q r) (a : Fin 2) :
    AdjacentSpinSwapAt (L+1) k (appendSpin L q a) (appendSpin L r a) := by
  induction h with
  | head L b c t h => exact .head (L+1) b c (appendSpin L t a) h
  | tail L k b h ih => exact .tail (L+1) k b ih

/-- The actual Hamiltonian,extended by zero only at the two lengths
where an adjacent physical pair does not exist. -/
def finitePhysicalHamiltonian (lam eta : ℝ) :
    (L : ℕ) → Matrix (RowSpins L) (RowSpins L) ℂ
  | 0 => 0
  | 1 => 0
  | n+2 => homogeneousLinkHamiltonian lam eta (n+1)

/-- The actual Hamiltonian entries are invariant under simultaneous
cyclic translation of the two configurations. -/
theorem finitePhysicalHamiltonian_cyclic_apply (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n : ℕ) (q r : RowSpins (n+1)) :
    finitePhysicalHamiltonian lam eta (n+1) (cyclicSpinTranslation n q) (cyclicSpinTranslation n r)=
      finitePhysicalHamiltonian lam eta (n+1) q r := by
  cases n with
  | zero => rfl
  | succ n =>
    change homogeneousLinkHamiltonian lam eta (n+1) (cyclicSpinTranslation (n+1) q)
      (cyclicSpinTranslation (n+1) r)=homogeneousLinkHamiltonian lam eta (n+1) q r
    have hc := homogeneousLinkHamiltonian_commutes lam eta h0 hpi (n+1) 0
    rw [homogeneousPhysicalRow_at_zero lam h0 hpi (n+1)] at hc
    have h := congrArg (fun A : Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ =>
      A (cyclicSpinTranslation (n+1) q) r) hc
    simpa only [mul_spinPermutation_apply (cyclicSpinTranslation (n+1)),
      spinPermutation_mul_apply (cyclicSpinTranslation (n+1)),Equiv.symm_apply_apply] using h

/-- Every indexed neighboring particle-hole swap has a strictly negative
entry in the actual Hamiltonian. -/
theorem finitePhysicalHamiltonian_swapAt_re_neg (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (k : ℕ) :
    ∀ (L : ℕ) (q r : RowSpins L),AdjacentSpinSwapAt L k q r →
      (finitePhysicalHamiltonian lam eta L q r).re<0 := by
  induction k with
  | zero =>
    intro L q r h
    cases h with
    | head n a b t hab =>
      exact homogeneousLinkHamiltonian_head_hop_re_neg lam eta h0 hpi heta n a b t hab
  | succ k ih =>
    intro L q r h
    cases h with
    | @tail m k a qt rt h =>
      rw [← finitePhysicalHamiltonian_cyclic_apply lam eta h0 hpi m (a,qt) (a,rt)]
      exact ih (m+1) (appendSpin m qt a) (appendSpin m rt a) (adjacentSpinSwapAt_append h a)

/-- All physical nearest-neighbor swaps are genuine strict negative
hopping edges of the actual full logarithmic row Hamiltonian. -/
theorem homogeneousLinkHamiltonian_adjacent_hop_re_neg (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n : ℕ) (q r : RowSpins (n+2))
    (h : AdjacentSpinSwap (n+2) q r) :
    (homogeneousLinkHamiltonian lam eta (n+1) q r).re<0 := by
  obtain ⟨k,hk⟩ := adjacentSpinSwap_exists_at h
  exact finitePhysicalHamiltonian_swapAt_re_neg lam eta h0 hpi heta k (n+2) q r hk

theorem adjacentSpinSwap_ne {L : ℕ} {q r : RowSpins L}
    (h : AdjacentSpinSwap L q r) : q≠r := by
  induction h with
  | head L a b t h =>
    intro he
    exact h (congrArg Prod.fst he)
  | tail L a h ih =>
    intro he
    exact ih (congrArg Prod.snd he)

/-- The graph uses the actual full Hamiltonian entry,not an assumed
nearest-neighbor graph. Its vertices are one exact particle sector. -/
def physicalSectorHoppingGraph (lam eta : ℝ) (n particles : ℕ) :
    SimpleGraph {q : RowSpins (n+2) // minusCount (n+2) q=particles} where
  Adj q r := q≠r ∧ (homogeneousLinkHamiltonian lam eta (n+1) q.val r.val).re<0
  symm := by
    constructor
    intro q r h
    refine ⟨h.1.symm,?_⟩
    have hh := congrArg (fun A : Matrix (RowSpins (n+2)) (RowSpins (n+2)) ℂ =>
      A q.val r.val) (homogeneousLinkHamiltonian_isHermitian lam eta n).eq
    have hr := congrArg Complex.re hh
    simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_re] at hr
    rw [hr]
    exact h.2
  loopless := by constructor;intro q h;exact h.1 rfl

/-- The actual Hamiltonian hopping graph is connected within every
particle sector. No connectivity hypothesis is assumed. -/
theorem physicalSectorHoppingGraph_preconnected (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n particles : ℕ) :
    (physicalSectorHoppingGraph lam eta n particles).Preconnected := by
  intro q r
  have hpath := spinSwapReach_of_minusCount_eq (n+2) q.val r.val (q.property.trans r.property.symm)
  have lift : ∀ {u v : RowSpins (n+2)},SpinSwapReach (n+2) u v →
      ∀ (hu : minusCount (n+2) u=particles) (hv : minusCount (n+2) v=particles),
      (physicalSectorHoppingGraph lam eta n particles).Reachable ⟨u,hu⟩ ⟨v,hv⟩ := by
    intro u v h
    induction h with
    | refl => intro hu hv;exact .refl _
    | @tail b c hab hbc ih =>
      intro hu hv
      have hb : minusCount (n+2) b=particles := (spinSwapReach_minusCount hab).symm.trans hu
      apply (ih hu hb).trans
      apply SimpleGraph.Adj.reachable
      refine ⟨?_,homogeneousLinkHamiltonian_adjacent_hop_re_neg lam eta h0 hpi heta n b c hbc⟩
      intro he
      exact adjacentSpinSwap_ne hbc (congrArg Subtype.val he)
  exact lift hpath q.property r.property

end
end SixVertex
