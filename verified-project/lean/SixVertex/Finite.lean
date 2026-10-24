import Std

/-!
# Six-vertex finite combinatorics

This file does NOT prove the GFF convergence theorem.

The arrow convention matches the square-lattice model: `west` and `east`
record whether their horizontal edges point east; `south` and `north`
record whether their vertical edges point north. Thus the ice rule is
conservation of positive-oriented arrow counts.

A `Column` glues vertices vertically. Its periodic conservation theorem
is the combinatorial reason a row transfer matrix preserves horizontal
arrow number, hence the balanced sector used in the manuscript.

No analytic model, infinite-volume probability law, or GFF is postulated.
-/

namespace SixVertex

/-- Indicator of an arrow pointing along the positive coordinate axis. -/
def bit (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem bit_false : bit false = 0 := rfl
@[simp] theorem bit_true : bit true = 1 := rfl

@[simp] theorem bit_complement (b : Bool) : bit (!b) + bit b = 1 := by
  cases b <;> decide

structure Vertex where
  west : Bool
  east : Bool
  south : Bool
  north : Bool
  deriving DecidableEq, Repr

/-- Conservation equation for a square-lattice vertex. -/
def Ice (v : Vertex) : Prop :=
  bit v.west + bit v.south = bit v.east + bit v.north

instance (v : Vertex) : Decidable (Ice v) := inferInstanceAs (Decidable (_ = _))

/-- Exactly two of the four arrows enter the vertex. -/
def TwoIncoming (v : Vertex) : Prop :=
  bit v.west + bit v.south + bit (!v.east) + bit (!v.north) = 2

instance (v : Vertex) : Decidable (TwoIncoming v) :=
  inferInstanceAs (Decidable (_ = _))

/-- Our oriented conservation convention is exactly the two-in/two-out rule. -/
theorem ice_iff_twoIncoming (v : Vertex) : Ice v ↔ TwoIncoming v := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> decide

/-- The six admissible vertices, with no duplicates. -/
def allowed : List Vertex :=
  [⟨false, false, false, false⟩, ⟨false, false, true, true⟩,
   ⟨true, true, false, false⟩, ⟨true, true, true, true⟩,
   ⟨true, false, false, true⟩, ⟨false, true, true, false⟩]

@[simp] theorem allowed_length : allowed.length = 6 := rfl

theorem allowed_nodup : allowed.Nodup := by decide

theorem ice_iff_mem_allowed (v : Vertex) : Ice v ↔ v ∈ allowed := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> decide

/-- The two vertices with both horizontal arrows inward or both outward. -/
def isC (v : Vertex) : Bool := v.west != v.east

theorem exactly_two_c_vertices : (allowed.filter isC).length = 2 := by decide

theorem exactly_four_unit_vertices : (allowed.filter fun v => !isC v).length = 4 := by
  decide

/-- Reverse every arrow. -/
def reverse (v : Vertex) : Vertex :=
  ⟨!v.west, !v.east, !v.south, !v.north⟩

@[simp] theorem reverse_reverse (v : Vertex) : reverse (reverse v) = v := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> rfl

@[simp] theorem ice_reverse (v : Vertex) : Ice (reverse v) ↔ Ice v := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> decide

@[simp] theorem isC_reverse (v : Vertex) : isC (reverse v) = isC v := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> rfl

/-- Number of horizontal arrows directed east at the west boundary. -/
def westCount (vs : List Vertex) : Nat := (vs.map fun v => bit v.west).sum

/-- Number of horizontal arrows directed east at the east boundary. -/
def eastCount (vs : List Vertex) : Nat := (vs.map fun v => bit v.east).sum

/-- Number of c-weighted vertices; a balanced-model configuration has
unnormalized weight c raised to this power. No probability claim is made here. -/
def cCount (vs : List Vertex) : Nat := (vs.map fun v => bit (isC v)).sum

@[simp] theorem cCount_reverse (vs : List Vertex) :
    cCount (vs.map reverse) = cCount vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [cCount, List.map_cons, List.sum_cons] using ih

/-- A vertically glued column with specified bottom and top boundary arrows. -/
inductive Column : Bool → Bool → List Vertex → Prop where
  | nil (b : Bool) : Column b b []
  | cons {top : Bool} {vs : List Vertex} (v : Vertex)
      (hv : Ice v) (tail : Column v.north top vs) :
      Column v.south top (v :: vs)

/-- All vertices in a glued column satisfy the ice rule. -/
theorem column_ice {b t : Bool} {vs : List Vertex} (h : Column b t vs) :
    ∀ v ∈ vs, Ice v := by
  induction h with
  | nil b => simp
  | cons v hv tail ih =>
      intro u hu
      rcases List.mem_cons.mp hu with huv | hu
      · subst u; exact hv
      · exact ih u hu

/-- Discrete divergence theorem: internal vertical edges cancel. -/
theorem column_flux {b t : Bool} {vs : List Vertex} (h : Column b t vs) :
    westCount vs + bit b = eastCount vs + bit t := by
  induction h with
  | nil b => rfl
  | cons v hv tail ih =>
      simp only [westCount, eastCount, List.map_cons, List.sum_cons] at ih ⊢
      unfold Ice at hv
      omega

/-- Periodic vertical gluing preserves the horizontal arrow count. -/
theorem periodic_sector_conservation {b : Bool} {vs : List Vertex}
    (h : Column b b vs) : westCount vs = eastCount vs := by
  have hf := column_flux h
  omega

/-- Exact balance avoids truncated natural-number division at odd sizes. -/
def BalancedWest (vs : List Vertex) : Prop := 2 * westCount vs = vs.length

def BalancedEast (vs : List Vertex) : Prop := 2 * eastCount vs = vs.length

/-- The balanced sector is invariant under an admissible periodic column. -/
theorem balanced_sector_preserved {b : Bool} {vs : List Vertex}
    (h : Column b b vs) : BalancedWest vs ↔ BalancedEast vs := by
  unfold BalancedWest BalancedEast
  rw [periodic_sector_conservation h]

/-- A balanced boundary has even length. -/
theorem balanced_length_even {vs : List Vertex} (h : BalancedWest vs) :
    vs.length % 2 = 0 := by
  unfold BalancedWest at h
  omega

/-- Reversing a finite boundary complements its east-pointing count. -/
theorem westCount_reverse (vs : List Vertex) :
    westCount (vs.map reverse) + westCount vs = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, westCount, List.sum_cons, List.length_cons] at ih ⊢
      have hv := bit_complement v.west
      change bit (!v.west) + (List.map (fun v => bit v.west) (List.map reverse vs)).sum +
        (bit v.west + (List.map (fun v => bit v.west) vs).sum) = vs.length + 1
      omega

/-- Arrow reversal stays within the balanced sector. -/
theorem balanced_reverse {vs : List Vertex} (h : BalancedWest vs) :
    BalancedWest (vs.map reverse) := by
  have hc := westCount_reverse vs
  unfold BalancedWest at h ⊢
  rw [List.length_map]
  omega

/-- Arrow reversal preserves periodic gluing and admissibility. -/
theorem column_reverse {b t : Bool} {vs : List Vertex} (h : Column b t vs) :
    Column (!b) (!t) (vs.map reverse) := by
  induction h with
  | nil b => exact Column.nil (!b)
  | cons v hv tail ih =>
      exact Column.cons (reverse v) ((ice_reverse v).mpr hv) ih

end SixVertex

#print axioms SixVertex.ice_iff_mem_allowed
#print axioms SixVertex.column_flux
#print axioms SixVertex.balanced_sector_preserved
#print axioms SixVertex.cCount_reverse
#print axioms SixVertex.column_reverse
