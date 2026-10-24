import SixVertex.PhysicalTransferPositive

namespace SixVertex
noncomputable section

/-- Exact first-pair exchange entry of an equal-weight row. -/
theorem markedRow_equal_head_hop (d c : ℂ) (n : ℕ) (a b : Fin 2) (t : RowSpins n)
    (hab : a≠b) :
    markedRow (fun _ => sixMatrix d d c) (n+2) 1 (a,b,t) (b,a,t)=c^2*d^n := by
  simp only [markedRow,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change (∑ u : Fin 2,∑ v : Fin 2,sixMatrix d d c (u,a) (v,b)*
    (∑ w : Fin 2,sixMatrix d d c (v,b) (w,a)*rowBlock (fun _ => sixMatrix d d c) n w u t t))= _
  simp_rw [rowBlock_equal_diagonal]
  fin_cases a <;> fin_cases b <;> simp_all [Fin.sum_univ_two,sixMatrix] <;> ring

/-- Actual homogeneous transfer entries are invariant under simultaneous
cyclic translation of their two configurations. -/
theorem homogeneousPhysicalRow_cyclic_apply (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi)
    (n : ℕ) (z : ℂ) (q r : RowSpins (n+1)) :
    homogeneousPhysicalRow lam (n+1) z (cyclicSpinTranslation n q) (cyclicSpinTranslation n r)=
      homogeneousPhysicalRow lam (n+1) z q r := by
  have hc := homogeneousPhysicalRows_commute lam h0 hpi (n+1) z 0
  rw [homogeneousPhysicalRow_at_zero lam h0 hpi n] at hc
  have h := congrArg (fun A : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ =>
    A (cyclicSpinTranslation n q) r) hc
  simpa only [mul_spinPermutation_apply (cyclicSpinTranslation n),
    spinPermutation_mul_apply (cyclicSpinTranslation n),Equiv.symm_apply_apply] using h

/-- The physical positive row contains each first-pair particle-hole hop
with its exact positive weight. -/
theorem homogeneousPhysicalRow_midpoint_head_hop (lam : ℝ) (n : ℕ)
    (a b : Fin 2) (t : RowSpins n) (hab : a≠b) :
    homogeneousPhysicalRow lam (n+2) ((lam : ℂ)/2) (a,b,t) (b,a,t)=
      (((Real.sin (lam/2)/Real.sin lam)^n : ℝ) : ℂ) := by
  change markedRow (fun _ => physicalR lam ((lam : ℂ)/2)) (n+2) 1 (a,b,t) (b,a,t)= _
  rw [show (fun _ : ℕ => physicalR lam ((lam : ℂ)/2))=
    (fun _ => sixMatrix ((Real.sin (lam/2)/Real.sin lam : ℝ) : ℂ)
      ((Real.sin (lam/2)/Real.sin lam : ℝ) : ℂ) 1) from funext (fun _ => physicalR_at_midpoint lam)]
  rw [markedRow_equal_head_hop _ _ n a b t hab]
  simp

theorem homogeneousPhysicalRow_midpoint_head_hop_re_pos (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n : ℕ) (a b : Fin 2) (t : RowSpins n) (hab : a≠b) :
    0<(homogeneousPhysicalRow lam (n+2) ((lam : ℂ)/2) (a,b,t) (b,a,t)).re := by
  rw [homogeneousPhysicalRow_midpoint_head_hop lam n a b t hab,Complex.ofReal_re]
  exact pow_pos (physical_midpoint_weight_pos lam h0 hpi) n

/-- Every indexed neighboring hop has a strictly positive actual
transfer entry;rotation decreases the index to the proved first pair. -/
theorem homogeneousPhysicalRow_midpoint_swapAt_re_pos (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (k : ℕ) :
    ∀ (L : ℕ) (q r : RowSpins L),AdjacentSpinSwapAt L k q r →
      0<(homogeneousPhysicalRow lam L ((lam : ℂ)/2) q r).re := by
  induction k with
  | zero =>
    intro L q r h
    cases h with
    | head n a b t hab =>
      exact homogeneousPhysicalRow_midpoint_head_hop_re_pos lam h0 hpi n a b t hab
  | succ k ih =>
    intro L q r h
    cases h with
    | @tail m k a qt rt h =>
      rw [← homogeneousPhysicalRow_cyclic_apply lam h0 hpi m ((lam : ℂ)/2) (a,qt) (a,rt)]
      exact ih (m+1) (appendSpin m qt a) (appendSpin m rt a) (adjacentSpinSwapAt_append h a)

theorem homogeneousPhysicalRow_midpoint_adjacent_hop_re_pos (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (L : ℕ) (q r : RowSpins L) (h : AdjacentSpinSwap L q r) :
    0<(homogeneousPhysicalRow lam L ((lam : ℂ)/2) q r).re := by
  obtain ⟨k,hk⟩ := adjacentSpinSwap_exists_at h
  exact homogeneousPhysicalRow_midpoint_swapAt_re_pos lam h0 hpi k L q r hk

/-- The graph is defined directly by positive entries of the actual
physical transfer row in both directions. -/
def physicalPositiveTransferGraph (lam : ℝ) (n particles : ℕ) :
    SimpleGraph (ParticleConfigurations (n+2) particles) where
  Adj q r := q≠r ∧ 0<(complexSectorTransfer lam n particles ((lam : ℂ)/2) q r).re ∧
    0<(complexSectorTransfer lam n particles ((lam : ℂ)/2) r q).re
  symm := by constructor;intro q r h;exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by constructor;intro q h;exact h.1 rfl

/-- The actual positive-entry transfer graph is connected in every
particle sector. No transfer irreducibility hypothesis is assumed. -/
theorem physicalPositiveTransferGraph_preconnected (lam : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (n particles : ℕ) :
    (physicalPositiveTransferGraph lam n particles).Preconnected := by
  intro q r
  have hpath := spinSwapReach_of_minusCount_eq (n+2) q.val r.val (q.property.trans r.property.symm)
  have lift : ∀ {u v : RowSpins (n+2)},SpinSwapReach (n+2) u v →
      ∀ (hu : minusCount (n+2) u=particles) (hv : minusCount (n+2) v=particles),
      (physicalPositiveTransferGraph lam n particles).Reachable ⟨u,hu⟩ ⟨v,hv⟩ := by
    intro u v h
    induction h with
    | refl => intro hu hv;exact .refl _
    | @tail b c hab hbc ih =>
      intro hu hv
      have hb : minusCount (n+2) b=particles := (spinSwapReach_minusCount hab).symm.trans hu
      apply (ih hu hb).trans
      apply SimpleGraph.Adj.reachable
      refine ⟨?_,homogeneousPhysicalRow_midpoint_adjacent_hop_re_pos lam h0 hpi (n+2) b c hbc,
        homogeneousPhysicalRow_midpoint_adjacent_hop_re_pos lam h0 hpi (n+2) c b (adjacentSpinSwap_symm hbc)⟩
      intro he
      exact adjacentSpinSwap_ne hbc (congrArg Subtype.val he)
  exact lift hpath q.property r.property

end
end SixVertex
