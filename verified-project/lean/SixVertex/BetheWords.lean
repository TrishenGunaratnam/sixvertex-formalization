import SixVertex.BetheCAction

namespace SixVertex

inductive RowEntry where
  | A | B | C | L
  deriving DecidableEq

noncomputable def entryOperator (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (e : RowEntry) (v : ℂ) : Matrix (RowSpins n) (RowSpins n) ℂ :=
  match e with
  | .A => betheA t b n v
  | .B => betheB t b n v
  | .C => betheC t b n v
  | .L => betheL t b n v

/-- Explicit choices at one step. The C choices retain both removal orders. -/
noncomputable def entryTerms (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (e : RowEntry) (v : ℂ) (U : Finset ℂ) : List (ℂ × Finset ℂ) := by
  classical
  let E := insert v U
  exact match e with
  | .B => [(1,E)]
  | .A => E.toList.map (fun p =>
      (vacuumA t b p n * betheBeta t (v-p) * ∏ x ∈ E.erase p, betheF t (x-p), E.erase p))
  | .L => E.toList.map (fun p =>
      (vacuumL t b p n * betheBeta t (p-v) * ∏ x ∈ E.erase p, betheF t (p-x), E.erase p))
  | .C => E.toList.flatMap (fun p => (E.erase p).toList.map
      (fun q => (cActionWeight t b n E v p q, (E.erase p).erase q)))

noncomputable def weightedEval {R : Type*} [AddCommMonoid R] [Module ℂ R]
    (V : Finset ℂ → R) (T : List (ℂ × Finset ℂ)) : R :=
  (T.map (fun z => z.1 • V z.2)).sum

theorem weightedEval_congr {R : Type*} [AddCommMonoid R] [Module ℂ R]
    (V W : Finset ℂ → R) (T : List (ℂ × Finset ℂ))
    (h : ∀ z ∈ T, V z.2 = W z.2) : weightedEval V T = weightedEval W T := by
  unfold weightedEval
  congr 1
  apply List.map_congr_left
  intro z hz
  rw [h z hz]

theorem weightedEval_scale {R : Type*} [AddCommMonoid R] [Module ℂ R]
    (V : Finset ℂ → R) (T : List (ℂ × Finset ℂ)) (a : ℂ) :
    weightedEval V (T.map (fun z => (a*z.1,z.2))) = a • weightedEval V T := by
  induction T with
  | nil => simp [weightedEval]
  | cons z T ih =>
    simpa only [weightedEval, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_def, smul_add, smul_smul] using congrArg (fun x => (a*z.1) • V z.2 + x) ih

theorem weightedEval_append {R : Type*} [AddCommMonoid R] [Module ℂ R]
    (V : Finset ℂ → R) (T Q : List (ℂ × Finset ℂ)) :
    weightedEval V (T++Q) = weightedEval V T + weightedEval V Q := by
  simp [weightedEval]

theorem weightedEval_bind {R : Type*} [AddCommMonoid R] [Module ℂ R]
    (V : Finset ℂ → R) (T : List (ℂ × Finset ℂ))
    (f : Finset ℂ → List (ℂ × Finset ℂ)) :
    weightedEval V (T.flatMap (fun z => (f z.2).map (fun w => (z.1*w.1,w.2)))) =
      weightedEval (fun U => weightedEval V (f U)) T := by
  induction T with
  | nil => simp [weightedEval]
  | cons z T ih =>
    rw [List.flatMap_cons, weightedEval_append, weightedEval_scale, ih]
    rfl

theorem weightedEval_mul_left {R : Type*} [Ring R] [Algebra ℂ R]
    (V : Finset ℂ → R) (T : List (ℂ × Finset ℂ)) (O : R) :
    O * weightedEval V T = weightedEval (fun U => O * V U) T := by
  induction T with
  | nil => simp [weightedEval]
  | cons z T ih =>
    simp only [weightedEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [mul_add, mul_smul_comm, ih]

theorem list_sum_flatMap {I R : Type*} [AddCommMonoid R] (U : List I) (f : I → List R) :
    (U.flatMap f).sum = (U.map (fun x => (f x).sum)).sum := by
  induction U with
  | nil => simp
  | cons x U ih => simp [List.flatMap_cons, ih]

theorem entry_expansion (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (e : RowEntry) (v : ℂ) (U : Finset ℂ)
    (hv : v ∉ U) (hreg : BetheRegular t (insert v U)) :
    entryOperator t b n e v * betheState t ht b n U =
      weightedEval (betheState t ht b n) (entryTerms t b n e v U) := by
  classical
  cases e with
  | A =>
    simpa [entryOperator, entryTerms, weightedEval, List.map_map, Function.comp_def,
      Finset.sum_map_toList] using bethe_A_action t ht b n U v hv hreg
  | B => simpa [entryOperator, entryTerms, weightedEval] using bethe_B_action t ht b n U v hv
  | L =>
    simpa [entryOperator, entryTerms, weightedEval, List.map_map, Function.comp_def,
      Finset.sum_map_toList] using bethe_L_action t ht b n U v hv hreg
  | C =>
    simpa [entryOperator, entryTerms, weightedEval, List.map_flatMap, List.map_map,
      list_sum_flatMap, Function.comp_def, Finset.sum_map_toList] using
      bethe_C_action t ht b n U v hv hreg

/-- Domain condition for a word of generic, fresh arguments. It keeps
all previously added arguments, even if a particular path removed them. -/
def WordRegular (t : ℂ) (U : Finset ℂ) : List (RowEntry × ℂ) → Prop
  | [] => True
  | (_,v)::w => v ∉ U ∧ BetheRegular t (insert v U) ∧ WordRegular t (insert v U) w

theorem WordRegular.mono {t : ℂ} {U S : Finset ℂ} (hSU : S ⊆ U)
    (w : List (RowEntry × ℂ)) (h : WordRegular t U w) : WordRegular t S w := by
  classical
  induction w generalizing U S with
  | nil => trivial
  | cons z w ih =>
    exact ⟨fun hs => h.1 (hSU hs), h.2.1.mono (Finset.insert_subset_insert z.2 hSU),
      ih (Finset.insert_subset_insert z.2 hSU) h.2.2⟩

noncomputable def wordOperator (t : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    List (RowEntry × ℂ) → Matrix (RowSpins n) (RowSpins n) ℂ
  | [] => 1
  | (e,v)::w => wordOperator t b n w * entryOperator t b n e v

/-- All weighted paths; repeated terminal sets are deliberately retained. -/
noncomputable def wordTerms (t : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    List (RowEntry × ℂ) → Finset ℂ → List (ℂ × Finset ℂ)
  | [], U => [(1,U)]
  | (e,v)::w, U => (entryTerms t b n e v U).flatMap
      (fun z => (wordTerms t b n w z.2).map (fun y => (z.1*y.1,y.2)))

/-- Each entry adds its argument and removes at most two elements. -/
theorem entryTerms_support (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (e : RowEntry)
    (v : ℂ) (U : Finset ℂ) (z : ℂ × Finset ℂ) (hz : z ∈ entryTerms t b n e v U) :
    z.2 ⊆ insert v U := by
  classical
  cases e <;> simp only [entryTerms] at hz
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact Finset.erase_subset _ _
  · simp only [List.mem_singleton] at hz
    subst z
    exact Finset.Subset.refl _
  · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact Finset.erase_subset _ _

theorem word_expansion (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (w : List (RowEntry × ℂ)) (U : Finset ℂ)
    (hreg : WordRegular t U w) :
    wordOperator t b n w * betheState t ht b n U =
      weightedEval (betheState t ht b n) (wordTerms t b n w U) := by
  induction w generalizing U with
  | nil => simp [wordOperator, wordTerms, weightedEval]
  | cons z w ih =>
    rcases z with ⟨e,v⟩
    rw [wordOperator, mul_assoc, entry_expansion t ht b n e v U hreg.1 hreg.2.1,
      weightedEval_mul_left, wordTerms, weightedEval_bind]
    apply weightedEval_congr
    intro z hz
    exact ih z.2 (hreg.2.2.mono (entryTerms_support t b n e v U z hz) w)

theorem entryTerms_remove_bound (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (e : RowEntry)
    (v : ℂ) (U : Finset ℂ) (z : ℂ × Finset ℂ) (hz : z ∈ entryTerms t b n e v U) :
    ((insert v U) \ z.2).card ≤ 2 := by
  classical
  have h1 : ∀ (E : Finset ℂ) (p : ℂ), (E \ E.erase p).card ≤ 2 := by
    intro E p
    have hs : E \ E.erase p ⊆ {p} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_erase, not_and] at hx
      simp only [Finset.mem_singleton]
      by_contra hn
      exact hx.2 hn hx.1
    have hh := Finset.card_le_card hs
    simpa using le_trans hh (by simp : ({p} : Finset ℂ).card ≤ 2)
  have h2 : ∀ (E : Finset ℂ) (p q : ℂ), (E \ (E.erase p).erase q).card ≤ 2 := by
    intro E p q
    have hs : E \ (E.erase p).erase q ⊆ {p,q} := by
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      by_cases hp : x = p
      · simp [hp]
      · by_cases hq : x = q
        · simp [hq]
        · exact False.elim (hx.2 (Finset.mem_erase.mpr ⟨hq, Finset.mem_erase.mpr ⟨hp,hx.1⟩⟩))
    have hh := Finset.card_le_card hs
    have hb : ({p,q} : Finset ℂ).card ≤ 2 := by
      simpa using Finset.card_insert_le p ({q} : Finset ℂ)
    exact hh.trans hb
  cases e <;> simp only [entryTerms] at hz
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact h1 _ _
  · simp only [List.mem_singleton] at hz
    subst z
    simp
  · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
    exact h2 _ _ _
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
    exact h1 _ _

theorem wordTerms_support (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (w : List (RowEntry × ℂ)) (U : Finset ℂ) (z : ℂ × Finset ℂ)
    (hz : z ∈ wordTerms t b n w U) : z.2 ⊆ U ∪ (w.map Prod.snd).toFinset := by
  classical
  induction w generalizing U z with
  | nil =>
    simp only [wordTerms, List.mem_singleton] at hz
    subst z
    simp
  | cons a w ih =>
    rcases a with ⟨e,v⟩
    obtain ⟨y, hy, hrest⟩ := List.mem_flatMap.mp hz
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hrest
    subst z
    have htail := ih y.2 q hq
    have hstep := entryTerms_support t b n e v U y hy
    intro x hx
    have hh := htail hx
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    rcases Finset.mem_union.mp hh with h | h
    · rcases Finset.mem_insert.mp (hstep h) with rfl | hu
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hu
    · exact Or.inr (Or.inr h)

/-- Equal endpoint cardinality forces the same number of absent original
roots and surviving new arguments, with at most one new argument per step. -/
theorem word_path_cardinality (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (w : List (RowEntry × ℂ)) (U : Finset ℂ) (z : ℂ × Finset ℂ)
    (hz : z ∈ wordTerms t b n w U) (hcard : z.2.card = U.card) :
    (U \ z.2).card = (z.2 \ U).card ∧ (z.2 \ U).card ≤ w.length := by
  classical
  have hsupport := wordTerms_support t b n w U z hz
  have hsub : z.2 \ U ⊆ (w.map Prod.snd).toFinset := by
    intro x hx
    have hh := hsupport (Finset.mem_sdiff.mp hx).1
    exact (Finset.mem_union.mp hh).resolve_left (Finset.mem_sdiff.mp hx).2
  have ha := Finset.card_sdiff_add_card_inter U z.2
  have hb := Finset.card_sdiff_add_card_inter z.2 U
  rw [Finset.inter_comm z.2 U] at hb
  have hc := Finset.card_le_card hsub
  have hd := (w.map Prod.snd).toFinset_card_le
  simp only [List.length_map] at hd
  exact ⟨by omega, hc.trans hd⟩

end SixVertex
