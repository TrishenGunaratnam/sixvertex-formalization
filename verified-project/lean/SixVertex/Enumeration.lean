import SixVertex.Transfer

/-!
Duplicate-free finite enumeration. A periodic-column record retains its seam
spin even at zero height. For positive height that spin is recovered from the
first vertex, so erasing the seam spin still gives a duplicate-free list.
-/

namespace SixVertex

/-- A nonempty column determines its bottom boundary spin. -/
theorem column_bottom_unique {b b' t t' : Bool} {vs : List Vertex}
    (h : Column b t vs) (h' : Column b' t' vs) (hne : vs ≠ []) : b = b' := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons v hv tail => cases h'; rfl

/-- Each glued admissible column is generated exactly once. -/
theorem columns_nodup (b : Bool) (n : Nat) : (columns b n).Nodup := by
  induction n generalizing b with
  | zero => simp [columns]
  | succ n ih =>
      unfold columns
      apply List.pairwise_flatMap.mpr
      constructor
      · intro v hv
        split
        next hb =>
          apply List.pairwise_map.mpr
          apply (ih v.north).imp
          intro p q hpq heq
          apply hpq
          rcases p with ⟨pt, ps⟩
          rcases q with ⟨qt, qs⟩
          simpa only [Prod.mk.injEq, List.cons.injEq, true_and] using heq
        next => simp
      · apply allowed_nodup.imp
        intro v w hvw p hp q hq heq
        by_cases hvb : v.south = b
        · simp only [ite_eq_left hvb, List.mem_map] at hp
          obtain ⟨ps, hps, rfl⟩ := hp
          by_cases hwb : w.south = b
          · simp only [ite_eq_left hwb, List.mem_map] at hq
            obtain ⟨qs, hqs, rfl⟩ := hq
            exact hvw (List.cons.inj (congrArg Prod.snd heq)).1
          · simp [hwb] at hq
        · simp [hvb] at hp

/-- Periodic glued columns with fixed left/right horizontal boundaries. -/
def periodicColumns (n : Nat) (left right : List Bool) : List (Bool × List Vertex) :=
  [false, true].flatMap fun b =>
    (columns b n).filter fun p =>
      p.1 == b && westState p.2 == left && eastState p.2 == right

theorem periodicColumns_sound {p : Bool × List Vertex} {n : Nat}
    {left right : List Bool} (h : p ∈ periodicColumns n left right) :
    Column p.1 p.1 p.2 ∧ p.2.length = n ∧ westState p.2 = left ∧
      eastState p.2 = right := by
  simp only [periodicColumns, List.mem_flatMap] at h
  obtain ⟨b, hb, hp⟩ := h
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hm, ⟨⟨ht, hl⟩, hr⟩⟩ := hp
  obtain ⟨hc, hn⟩ := columns_sound hm
  rw [ht] at hc
  rw [ht]
  exact ⟨hc, hn, hl, hr⟩

theorem periodicColumns_complete {b : Bool} {vs : List Vertex}
    (h : Column b b vs) :
    (b, vs) ∈ periodicColumns vs.length (westState vs) (eastState vs) := by
  simp only [periodicColumns, List.mem_flatMap]
  refine ⟨b, ?_, ?_⟩
  · cases b <;> simp
  · simp only [List.mem_filter, beq_self_eq_true, Bool.and_self, and_true]
    exact columns_complete h

/-- Seam-labelled periodic configurations have no duplicates, even at height zero. -/
theorem periodicColumns_nodup (n : Nat) (left right : List Bool) :
    (periodicColumns n left right).Nodup := by
  unfold periodicColumns
  apply List.pairwise_flatMap.mpr
  constructor
  · intro b hb
    exact (columns_nodup b n).filter _
  · apply (show ([false, true] : List Bool).Nodup by decide).imp
    intro b b' hbb p hp q hq hpq
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hp hq
    apply hbb
    exact hp.2.1.1.symm.trans ((congrArg Prod.fst hpq).trans hq.2.1.1)

/-- For a genuine positive-height column, the list of vertices has no multiplicity. -/
theorem periodicColumns_vertices_nodup {n : Nat} (hn : 0 < n)
    (left right : List Bool) :
    ((periodicColumns n left right).map Prod.snd).Nodup := by
  apply List.pairwise_map.mpr
  apply (periodicColumns_nodup n left right).imp_of_mem
  intro p q hp hq hpq heq
  apply hpq
  have hp' := periodicColumns_sound hp
  have hq' := periodicColumns_sound hq
  have hne : p.2 ≠ [] := by
    intro hz
    have hlen := hp'.2.1
    rw [hz] at hlen
    simp at hlen
    omega
  have hbottom : p.1 = q.1 :=
    column_bottom_unique hp'.1 (heq ▸ hq'.1) hne
  exact Prod.ext hbottom heq

/-- The original exponent kernel is precisely the image of the configuration list. -/
theorem transferExponents_eq_periodicColumns (n : Nat) (left right : List Bool) :
    transferExponents n left right =
      (periodicColumns n left right).map (fun p => cCount p.2) := rfl

/-- Transfer entries vanish identically between different conserved sectors. -/
theorem transferExponents_empty_of_sector_ne {n : Nat} {left right : List Bool}
    (hne : (left.map bit).sum ≠ (right.map bit).sum) :
    transferExponents n left right = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro k hk
  exact hne (transfer_sector_support hk)

/-- Every monomial has degree at most the number of vertices in the column. -/
theorem transferExponents_degree_le {n k : Nat} {left right : List Bool}
    (h : k ∈ transferExponents n left right) : k ≤ n := by
  obtain ⟨b, vs, hc, hn, hl, hr, hk⟩ := transferExponents_sound h
  have bound : ∀ us : List Vertex, cCount us ≤ us.length := by
    intro us
    induction us with
    | nil => simp [cCount]
    | cons v us ih =>
        have hv : bit (isC v) ≤ 1 := by cases isC v <;> decide
        simp only [cCount, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
        omega
  rw [← hk, ← hn]
  exact bound vs

end SixVertex
