import SixVertex.Finite

/-!
An exact finite-column enumerator and a symbolic transfer kernel. A kernel is
a list of exponents: an exponent k contributes the monomial c^k. This keeps
the model independent of the eventual real/complex coefficient library.
Soundness, completeness, sector support and balanced witnesses are proved
here. Enumeration without duplicates and the torus trace identity are still
pending; no normalized probability or analytic transfer theorem is claimed.
-/

namespace SixVertex

def westState (vs : List Vertex) : List Bool := vs.map (·.west)
def eastState (vs : List Vertex) : List Bool := vs.map (·.east)

/-- Enumerate glued admissible columns from a fixed bottom spin. -/
def columns (bottom : Bool) : Nat → List (Bool × List Vertex)
  | 0 => [(bottom, [])]
  | n + 1 => allowed.flatMap fun v =>
      if v.south = bottom then
        (columns v.north n).map fun p => (p.1, v :: p.2)
      else []

theorem columns_sound {b t : Bool} {vs : List Vertex} {n : Nat}
    (h : (t, vs) ∈ columns b n) : Column b t vs ∧ vs.length = n := by
  induction n generalizing b t vs with
  | zero =>
      simp only [columns, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at h
      rcases h with ⟨ht, hvs⟩
      subst t
      subst vs
      exact ⟨Column.nil _, rfl⟩
  | succ n ih =>
      simp only [columns, List.mem_flatMap] at h
      obtain ⟨v, hv, hh⟩ := h
      split at hh
      next hb =>
        simp only [List.mem_map, Prod.mk.injEq] at hh
        obtain ⟨⟨u, us⟩, hu, ht, hvs⟩ := hh
        obtain ⟨hc, hl⟩ := ih hu
        subst t
        subst vs
        subst b
        exact ⟨Column.cons v ((ice_iff_mem_allowed v).mpr hv) hc,
          by simp [hl]⟩
      next => simp at hh

theorem columns_complete {b t : Bool} {vs : List Vertex}
    (h : Column b t vs) : (t, vs) ∈ columns b vs.length := by
  induction h with
  | nil b => simp [columns]
  | @cons t vs v hv tail ih =>
      simp only [List.length_cons, columns, List.mem_flatMap]
      refine ⟨v, (ice_iff_mem_allowed v).mp hv, ?_⟩
      simp only [ite_true, List.mem_map]
      exact ⟨(t, vs), ih, rfl⟩

/-- Monomial exponents for a periodic column between two boundary states. -/
def transferExponents (n : Nat) (left right : List Bool) : List Nat :=
  ([false, true].flatMap fun b =>
    (columns b n).filter fun p =>
      p.1 == b && westState p.2 == left && eastState p.2 == right).map
        fun p => cCount p.2

theorem transferExponents_sound {n k : Nat} {left right : List Bool}
    (h : k ∈ transferExponents n left right) :
    ∃ b vs, Column b b vs ∧ vs.length = n ∧ westState vs = left ∧
      eastState vs = right ∧ cCount vs = k := by
  simp only [transferExponents, List.mem_map, List.mem_flatMap] at h
  obtain ⟨⟨t, vs⟩, ⟨b, hb, hp⟩, hk⟩ := h
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hm, ⟨⟨ht, hl⟩, hr⟩⟩ := hp
  obtain ⟨hc, hn⟩ := columns_sound hm
  subst t
  exact ⟨b, vs, hc, hn, hl, hr, hk⟩

theorem transferExponents_complete {b : Bool} {vs : List Vertex}
    (h : Column b b vs) :
    cCount vs ∈ transferExponents vs.length (westState vs) (eastState vs) := by
  simp only [transferExponents, List.mem_map, List.mem_flatMap]
  refine ⟨(b, vs), ⟨b, ?_, ?_⟩, rfl⟩
  · cases b <;> simp
  · simp only [List.mem_filter, beq_self_eq_true, Bool.and_self, and_true]
    exact columns_complete h

theorem transfer_sector_support {n k : Nat} {left right : List Bool}
    (h : k ∈ transferExponents n left right) :
    (left.map bit).sum = (right.map bit).sum := by
  obtain ⟨b, vs, hc, hn, hl, hr, hk⟩ := transferExponents_sound h
  rw [← hl, ← hr]
  simpa [westState, eastState, westCount, eastCount, List.map_map, Function.comp_def] using
    periodic_sector_conservation hc

theorem transfer_balanced_support {n k : Nat} {left right : List Bool}
    (h : k ∈ transferExponents n left right)
    (hb : 2 * (left.map bit).sum = n) :
    2 * (right.map bit).sum = n := by
  rw [← transfer_sector_support h]
  exact hb

/-- A balanced, c-free periodic column exists at every even height. -/
def balancedWitness (b : Bool) : Nat → List Vertex
  | 0 => []
  | n + 1 => ⟨false, false, b, b⟩ :: ⟨true, true, b, b⟩ :: balancedWitness b n

theorem balancedWitness_column (b : Bool) (n : Nat) :
    Column b b (balancedWitness b n) := by
  induction n with
  | zero => exact Column.nil b
  | succ n ih =>
      exact Column.cons ⟨false, false, b, b⟩ (by cases b <;> decide)
        (Column.cons ⟨true, true, b, b⟩ (by cases b <;> decide) ih)

@[simp] theorem balancedWitness_length (b : Bool) (n : Nat) :
    (balancedWitness b n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [balancedWitness, List.length_cons, ih]; omega

@[simp] theorem balancedWitness_westCount (b : Bool) (n : Nat) :
    westCount (balancedWitness b n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [balancedWitness, westCount, List.map_cons, List.sum_cons,
        bit_false, bit_true] at ih ⊢
      omega

@[simp] theorem balancedWitness_cCount (b : Bool) (n : Nat) :
    cCount (balancedWitness b n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [balancedWitness, cCount, isC, bit] using ih

theorem balancedWitness_balanced (b : Bool) (n : Nat) :
    BalancedWest (balancedWitness b n) := by
  simp [BalancedWest]

theorem balancedWitness_zero_monomial (b : Bool) (n : Nat) :
    0 ∈ transferExponents (2 * n) (westState (balancedWitness b n))
      (eastState (balancedWitness b n)) := by
  simpa using transferExponents_complete (balancedWitness_column b n)

end SixVertex
