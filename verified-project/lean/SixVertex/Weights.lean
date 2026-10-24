import SixVertex.Enumeration
import Init.Data.Rat.Lemmas

/-!
Exact rational Boltzmann weights for a single periodic column with fixed
horizontal boundary states. Positive rational c is an executable subcase of
the paper's real parameter. This file does not claim the real-valued model,
the torus trace formula, or an infinite-volume probability measure.
-/

namespace SixVertex

/-- Evaluate the symbolic monomial list at an exact rational parameter. -/
def exponentSum (c : Rat) (ks : List Nat) : Rat :=
  (ks.map fun k => c ^ k).sum

theorem exponentSum_nonneg {c : Rat} (hc : 0 ≤ c) (ks : List Nat) :
    0 ≤ exponentSum c ks := by
  induction ks with
  | nil => exact Rat.le_refl
  | cons k ks ih =>
      exact Rat.add_nonneg (Rat.pow_nonneg hc) ih

theorem exponentSum_pos_iff {c : Rat} (hc : 0 < c) (ks : List Nat) :
    0 < exponentSum c ks ↔ ks ≠ [] := by
  cases ks with
  | nil => simp [exponentSum, Rat.lt_irrefl]
  | cons k ks =>
      have hk : 0 < c ^ k := Rat.pow_pos hc
      have hs := exponentSum_nonneg (Rat.le_of_lt hc) ks
      have hp : 0 < c ^ k + exponentSum c ks := by grind
      constructor
      · intro _ hnil
        cases hnil
      · intro _
        exact hp

/-- A constant monomial ensures positive mass even at c=0. -/
theorem exponentSum_pos_of_zero_mem {c : Rat} (hc : 0 ≤ c) {ks : List Nat}
    (hzero : 0 ∈ ks) : 0 < exponentSum c ks := by
  induction ks with
  | nil => simp at hzero
  | cons k ks ih =>
      have hk := Rat.pow_nonneg (n := k) hc
      have hs := exponentSum_nonneg hc ks
      simp only [List.mem_cons] at hzero
      change 0 < c ^ k + exponentSum c ks
      rcases hzero with h | h
      · subst k
        simp only [Rat.pow_zero]
        grind
      · have hp := ih h
        grind

/-- Rational transfer weight, with every admissible column counted once. -/
def rationalTransfer (c : Rat) (n : Nat) (left right : List Bool) : Rat :=
  exponentSum c (transferExponents n left right)

theorem rationalTransfer_eq_sum_columns (c : Rat) (n : Nat)
    (left right : List Bool) :
    rationalTransfer c n left right =
      ((periodicColumns n left right).map fun p => c ^ cCount p.2).sum := by
  simp only [rationalTransfer, exponentSum, transferExponents_eq_periodicColumns,
    List.map_map, Function.comp_def]

theorem rationalTransfer_nonneg {c : Rat} (hc : 0 ≤ c) (n : Nat)
    (left right : List Bool) : 0 ≤ rationalTransfer c n left right :=
  exponentSum_nonneg hc _

/-- Exact positivity criterion in terms of genuine admissible periodic columns. -/
theorem rationalTransfer_pos_iff {c : Rat} (hc : 0 < c) (n : Nat)
    (left right : List Bool) :
    0 < rationalTransfer c n left right ↔
      ∃ b vs, Column b b vs ∧ vs.length = n ∧ westState vs = left ∧
        eastState vs = right := by
  rw [rationalTransfer, exponentSum_pos_iff hc]
  constructor
  · intro hne
    have hm : ∃ k, k ∈ transferExponents n left right := by
      cases heq : transferExponents n left right with
      | nil => exact False.elim (hne heq)
      | cons k ks => exact ⟨k, by simp⟩
    obtain ⟨k, hk⟩ := hm
    obtain ⟨b, vs, hcol, hn, hl, hr, _⟩ := transferExponents_sound hk
    exact ⟨b, vs, hcol, hn, hl, hr⟩
  · rintro ⟨b, vs, hcol, hn, hl, hr⟩ hempty
    have hm := transferExponents_complete hcol
    rw [hn, hl, hr, hempty] at hm
    simp at hm

/-- Different arrow-count sectors have identically zero transfer weight. -/
theorem rationalTransfer_zero_of_sector_ne (c : Rat) {n : Nat}
    {left right : List Bool}
    (hne : (left.map bit).sum ≠ (right.map bit).sum) :
    rationalTransfer c n left right = 0 := by
  rw [rationalTransfer, transferExponents_empty_of_sector_ne hne]
  rfl

/-- Balanced sectors have a positive diagonal weight at every even height. -/
theorem rationalTransfer_balanced_positive {c : Rat} (hc : 0 ≤ c)
    (b : Bool) (n : Nat) :
    0 < rationalTransfer c (2 * n) (westState (balancedWitness b n))
      (eastState (balancedWitness b n)) :=
  exponentSum_pos_of_zero_mem hc (balancedWitness_zero_monomial b n)

/-- Divide all monomial weights by one common nonzero normalizer. -/
theorem exponentSum_divide (c z : Rat) (ks : List Nat) :
    (ks.map fun k => c ^ k / z).sum = exponentSum c ks / z := by
  induction ks with
  | nil => simp [exponentSum, Rat.div_def]
  | cons k ks ih =>
      simp only [exponentSum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp only [Rat.div_def, Rat.add_mul]

/-- Probability mass on the complete, duplicate-free seam-labelled column space. -/
def columnProbability (c : Rat) (n : Nat) (left right : List Bool)
    (p : Bool × List Vertex) : Rat :=
  if p ∈ periodicColumns n left right then
    c ^ cCount p.2 / rationalTransfer c n left right
  else 0

theorem columnProbability_zero_of_not_mem (c : Rat) (n : Nat)
    (left right : List Bool) (p : Bool × List Vertex)
    (hp : p ∉ periodicColumns n left right) :
    columnProbability c n left right p = 0 := by
  simp only [columnProbability, ite_eq_right hp]

/-- Every admissible column has positive probability when c is positive. -/
theorem columnProbability_positive {c : Rat} (hc : 0 < c) {n : Nat}
    {left right : List Bool} {p : Bool × List Vertex}
    (hp : p ∈ periodicColumns n left right) :
    0 < columnProbability c n left right p := by
  have hs := periodicColumns_sound hp
  have hz : 0 < rationalTransfer c n left right :=
    (rationalTransfer_pos_iff hc n left right).mpr
      ⟨p.1, p.2, hs.1, hs.2⟩
  simp only [columnProbability, ite_eq_left hp, Rat.div_def]
  exact Rat.mul_pos (Rat.pow_pos hc) (Rat.inv_pos.mpr hz)

/-- Nonnegativity holds on all column records, including inadmissible ones. -/
theorem columnProbability_nonneg {c : Rat} (hc : 0 < c) (n : Nat)
    (left right : List Bool) (p : Bool × List Vertex) :
    0 ≤ columnProbability c n left right p := by
  by_cases hp : p ∈ periodicColumns n left right
  · exact Rat.le_of_lt (columnProbability_positive hc hp)
  · rw [columnProbability_zero_of_not_mem c n left right p hp]
    exact Rat.le_refl

/-- The conditional finite-column probability law has total mass exactly one. -/
theorem columnProbability_sum_one {c : Rat} (hc : 0 < c) {n : Nat}
    {left right : List Bool} (hne : periodicColumns n left right ≠ []) :
    ((periodicColumns n left right).map
      (columnProbability c n left right)).sum = 1 := by
  have hz : 0 < rationalTransfer c n left right := by
    apply (rationalTransfer_pos_iff hc n left right).mpr
    have hm : ∃ p, p ∈ periodicColumns n left right := by
      cases heq : periodicColumns n left right with
      | nil => exact False.elim (hne heq)
      | cons p ps => exact ⟨p, by simp⟩
    obtain ⟨p, hp⟩ := hm
    have hs := periodicColumns_sound hp
    exact ⟨p.1, p.2, hs.1, hs.2⟩
  have hmap : (periodicColumns n left right).map (columnProbability c n left right) =
      (periodicColumns n left right).map
        (fun p => c ^ cCount p.2 / rationalTransfer c n left right) := by
    apply List.map_congr_left
    intro p hp
    simp only [columnProbability, ite_eq_left hp]
  rw [hmap]
  have hdiv := exponentSum_divide c (rationalTransfer c n left right)
    (transferExponents n left right)
  rw [transferExponents_eq_periodicColumns] at hdiv
  simp only [List.map_map, Function.comp_def] at hdiv
  rw [hdiv]
  exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hz)

end SixVertex
