import SixVertex.PathDeterminants

namespace SixVertex

noncomputable def markedEntryChoices (D : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    List (ℂ × (RowEntry × ℂ)) :=
  [(D 0 0,(.A,x)),(D 1 0,(.B,x)),(D 0 1,(.C,x)),(D 1 1,(.L,x))]

noncomputable def markedWordChoices :
    List (Matrix (Fin 2) (Fin 2) ℂ × ℂ) → List (ℂ × List (RowEntry × ℂ))
  | [] => [(1,[])]
  | (D,x)::w => (markedEntryChoices D x).flatMap
      (fun z => (markedWordChoices w).map (fun q => (z.1*q.1,z.2::q.2)))

noncomputable def normalizedMarkedRow {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (D : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    Matrix (RowSpins L) (RowSpins L) ℂ :=
  (((-1 : ℂ)^n*betheTau lam b L Y 0 x)⁻¹) •
    markedRow (fun j => physicalTile lam (b j) x) L D

noncomputable def normalizedMarkedWord {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ) →
    Matrix (RowSpins L) (RowSpins L) ℂ
  | [] => 1
  | (D,x)::w => normalizedMarkedWord lam b L Y w * normalizedMarkedRow lam b L Y D x

theorem normalizedMarkedRow_entries {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (D : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    normalizedMarkedRow lam b L Y D x =
      D 0 0 • normalizedPhysicalEntry lam b L Y .A x +
      D 1 0 • normalizedPhysicalEntry lam b L Y .B x +
      D 0 1 • normalizedPhysicalEntry lam b L Y .C x +
      D 1 1 • normalizedPhysicalEntry lam b L Y .L x := by
  simp only [normalizedMarkedRow, markedRow, Fin.sum_univ_two,
    normalizedPhysicalEntry, physicalEntry, smul_add, smul_smul]
  module

theorem list_sum_mul_right {R : Type*} [NonUnitalNonAssocSemiring R] (xs : List R) (a : R) :
    xs.sum*a = (xs.map (fun x => x*a)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [add_mul,ih]

/-- Auxiliary marks are expanded entry by entry, with the manuscript's
D_{beta,alpha} convention and the original operator order. -/
theorem marked_word_entry_expansion {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) :
    normalizedMarkedWord lam b L Y w =
      ((markedWordChoices w).map (fun z => z.1 • normalizedPhysicalWord lam b L Y z.2)).sum := by
  induction w with
  | nil => simp [normalizedMarkedWord,markedWordChoices,normalizedPhysicalWord]
  | cons ev w ih =>
    rcases ev with ⟨D,x⟩
    simp [normalizedMarkedWord, normalizedMarkedRow_entries, ih, mul_add,
      mul_smul_comm, list_sum_mul_right, markedWordChoices, markedEntryChoices,
      normalizedPhysicalWord, smul_smul, smul_mul_assoc, List.smul_sum,
      mul_comm,mul_left_comm,mul_assoc,add_assoc,Function.comp_def]

/-- Every expanded entry word has exactly the same ordered spectral arguments. -/
theorem markedWordChoices_arguments (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ))
    (z : ℂ × List (RowEntry × ℂ)) (hz : z ∈ markedWordChoices w) :
    z.2.map Prod.snd = w.map Prod.snd := by
  induction w generalizing z with
  | nil => simp only [markedWordChoices,List.mem_singleton] at hz; subst z; rfl
  | cons ev w ih =>
    rcases ev with ⟨D,x⟩
    obtain ⟨y,hy,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have harg : y.2.2 = x := by
      simp [markedEntryChoices] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> rfl
    simp only [List.map_cons,harg,ih q hq]

end SixVertex
