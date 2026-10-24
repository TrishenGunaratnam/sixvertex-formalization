import SixVertex.PhysicalWords

namespace SixVertex

/-- Corrections with an arbitrary scalar decoration at each input state.
This records the physical parity without merging paths with equal endpoints. -/
noncomputable def decoratedCorrectionWords (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (eta : Finset ℂ → RowEntry → ℂ → ℂ) :
    List (RowEntry × ℂ) → Finset ℂ → List (ℂ × Finset ℂ)
  | [], U => [(1,U)]
  | (e,v)::w, U => (correctionEntryTerms t b L Y e v U).flatMap
      (fun z => (decoratedCorrectionWords t b L Y eta w z.2).map
        (fun y => (eta U e v*z.1*y.1,y.2)))

theorem decoratedCorrectionWords_support (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (eta : Finset ℂ → RowEntry → ℂ → ℂ) (w : List (RowEntry × ℂ))
    (U : Finset ℂ) (z : ℂ × Finset ℂ)
    (hz : z ∈ decoratedCorrectionWords t b L Y eta w U) :
    z.2 ⊆ U ∪ (w.map Prod.snd).toFinset := by
  classical
  induction w generalizing U z with
  | nil =>
    simp only [decoratedCorrectionWords, List.mem_singleton] at hz
    subst z
    simp
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    obtain ⟨y,hy,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have htail := ih y.2 q hq
    have hstep := correctionEntryTerms_support t b L Y e v U y hy
    intro x hx
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    rcases Finset.mem_union.mp (htail hx) with h | h
    · rcases Finset.mem_insert.mp (hstep h) with rfl | hu
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hu
    · exact Or.inr (Or.inr h)

/-- Physical signs included, the same vacuum potentials telescope exactly. -/
theorem physicalWordTerms_path_factorization (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y S U : Finset ℂ)
    (hY : Y ⊆ S) (hU : U ⊆ S) (w : List (RowEntry × ℂ))
    (hw : ∀ ev ∈ w, ev.2 ∈ S) (hreg : BetheRegular t S)
    (ha : ∀ p ∈ S, vacuumA t b p L ≠ 0) (hShell : BalancedRoots t b L 0 Y)
    (hfresh : WordRegular t U w) :
    physicalWordTerms t b L w U =
      (decoratedCorrectionWords t b L Y (fun V _ _ => (-1 : ℂ)^V.card) w U).map
      (fun z => (vacuumPotential t b L Y U * addedVacuumProduct t b L Y w /
        vacuumPotential t b L Y z.2 * z.1,z.2)) := by
  classical
  induction w generalizing U with
  | nil =>
    have hn := vacuumPotential_ne_zero t b L Y S U hY hU hreg ha
    simp [physicalWordTerms, decoratedCorrectionWords, addedVacuumProduct, hn]
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    have hv : v ∈ S := hw (e,v) (by simp)
    have htail : ∀ ev ∈ w, ev.2 ∈ S := fun ev hev => hw ev (by simp [hev])
    rw [physicalWordTerms, entryTerms_path_factorization t b L Y S U hY hU v hv e hreg ha hShell]
    simp only [decoratedCorrectionWords, List.flatMap_map, List.map_flatMap, List.map_map,
      Function.comp_def]
    apply List.flatMap_congr
    intro z hz
    have hzU := correctionEntryTerms_support t b L Y e v U z hz
    have hzS : z.2 ⊆ S := hzU.trans (Finset.insert_subset hv hU)
    rw [ih z.2 hzS htail (hfresh.2.2.mono hzU w)]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro y hy
    have hyS : y.2 ⊆ S := by
      intro x hx
      rcases Finset.mem_union.mp
        (decoratedCorrectionWords_support t b L Y (fun V _ _ => (-1 : ℂ)^V.card) w z.2 y hy hx) with h | h
      · exact hzS h
      · obtain ⟨ev,hev,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
        exact heq ▸ htail ev hev
    have hnz := vacuumPotential_ne_zero t b L Y S z.2 hY hzS hreg ha
    have hny := vacuumPotential_ne_zero t b L Y S y.2 hY hyS hreg ha
    have hE : vacuumPotential t b L Y (insert v U) =
        pathVacuumBase t b L Y v * vacuumPotential t b L Y U := Finset.prod_insert hfresh.1
    simp only [addedVacuumProduct, List.map_cons, List.prod_cons]
    congr 1
    rw [hE]
    field_simp
    <;> ring

/-- A scalar common to every step factors out once per word letter. -/
theorem decoratedCorrectionWords_scale (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (eta : Finset ℂ → RowEntry → ℂ → ℂ) (a : ℂ)
    (w : List (RowEntry × ℂ)) (U : Finset ℂ) :
    decoratedCorrectionWords t b L Y (fun V e v => a*eta V e v) w U =
      (decoratedCorrectionWords t b L Y eta w U).map (fun z => (a^w.length*z.1,z.2)) := by
  induction w generalizing U with
  | nil => simp [decoratedCorrectionWords]
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    simp only [decoratedCorrectionWords, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro z hz
    rw [ih]
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro y hy
    congr 1
    simp only [List.length_cons, pow_succ]
    ring

end SixVertex
