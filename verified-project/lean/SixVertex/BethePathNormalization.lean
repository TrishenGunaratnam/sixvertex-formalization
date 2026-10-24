import SixVertex.BethePathFactors

namespace SixVertex

noncomputable def vacuumPotential (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y U : Finset ℂ) : ℂ :=
  ∏ p ∈ U, pathVacuumBase t b L Y p

noncomputable def correctionEntryTerms (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (e : RowEntry) (v : ℂ) (U : Finset ℂ) : List (ℂ × Finset ℂ) := by
  classical
  let E := insert v U
  exact match e with
  | .B => [(1,E)]
  | .A => E.toList.map (fun p => (upperPathCorrection t Y (E.erase p) v p,E.erase p))
  | .L => E.toList.map (fun p => (lowerPathCorrection t b L Y (E.erase p) v p,E.erase p))
  | .C => E.toList.flatMap (fun p => (E.erase p).toList.map (fun q =>
      (doublePathCorrection t b L Y ((E.erase p).erase q) v p q,(E.erase p).erase q)))

theorem product_erase_ratio (f : ℂ → ℂ) (E : Finset ℂ) (p : ℂ) (hp : p ∈ E)
    (hf : ∀ x ∈ E, f x ≠ 0) : (∏ x ∈ E, f x)/(∏ x ∈ E.erase p, f x) = f p := by
  have hn : (∏ x ∈ E.erase p, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun x hx => hf x (Finset.mem_of_mem_erase hx))
  rw [← Finset.mul_prod_erase E f hp, mul_div_cancel_right₀ _ hn]

theorem product_double_erase_ratio (f : ℂ → ℂ) (E : Finset ℂ) (p q : ℂ)
    (hp : p ∈ E) (hq : q ∈ E.erase p) (hf : ∀ x ∈ E, f x ≠ 0) :
    (∏ x ∈ E, f x)/(∏ x ∈ (E.erase p).erase q, f x) = f p*f q := by
  have hn : (∏ x ∈ (E.erase p).erase q, f x) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun x hx => hf x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
  rw [← Finset.mul_prod_erase E f hp, ← Finset.mul_prod_erase (E.erase p) f hq]
  field_simp

/-- Each raw transition is its gamma correction times the exact ratio of
vacuum potentials before and after the removal. -/
theorem entryTerms_path_factorization (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y S U : Finset ℂ)
    (hY : Y ⊆ S) (hU : U ⊆ S) (v : ℂ) (hv : v ∈ S) (e : RowEntry)
    (hreg : BetheRegular t S) (ha : ∀ p ∈ S, vacuumA t b p L ≠ 0)
    (hShell : BalancedRoots t b L 0 Y) :
    entryTerms t b L e v U = (correctionEntryTerms t b L Y e v U).map
      (fun z => (vacuumPotential t b L Y (insert v U)/vacuumPotential t b L Y z.2*z.1,z.2)) := by
  classical
  have hE : insert v U ⊆ S := Finset.insert_subset hv hU
  have hbase : ∀ p ∈ insert v U, pathVacuumBase t b L Y p ≠ 0 := fun p hp =>
    pathVacuumBase_ne_zero t b L Y S hY p (hE hp) hreg (ha p (hE hp))
  cases e with
  | B =>
    have hn : vacuumPotential t b L Y (insert v U) ≠ 0 := Finset.prod_ne_zero_iff.mpr hbase
    simp [entryTerms, correctionEntryTerms, hn]
  | A =>
    simp only [entryTerms, correctionEntryTerms, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    have hpE : p ∈ insert v U := by simpa using hp
    have hr := product_erase_ratio (pathVacuumBase t b L Y) (insert v U) p hpE hbase
    have hc := upper_path_coefficient t b L Y ((insert v U).erase p) S p v hY
      ((Finset.erase_subset _ _).trans hE) (hE hpE) (Finset.notMem_erase _ _) hreg
    change (_,_) = (_, _)
    congr 1
    change _ = ((∏ x ∈ insert v U, pathVacuumBase t b L Y x)/
      (∏ x ∈ (insert v U).erase p, pathVacuumBase t b L Y x))*_
    rw [hr]
    exact hc.symm
  | L =>
    simp only [entryTerms, correctionEntryTerms, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    have hpE : p ∈ insert v U := by simpa using hp
    have hr := product_erase_ratio (pathVacuumBase t b L Y) (insert v U) p hpE hbase
    have hc := lower_path_coefficient t b L Y ((insert v U).erase p) S p v hY
      ((Finset.erase_subset _ _).trans hE) (hE hpE) (Finset.notMem_erase _ _) hreg (ha p (hE hpE)) hShell
    congr 1
    change _ = ((∏ x ∈ insert v U, pathVacuumBase t b L Y x)/
      (∏ x ∈ (insert v U).erase p, pathVacuumBase t b L Y x))*_
    rw [hr]
    exact hc.symm
  | C =>
    simp only [entryTerms, correctionEntryTerms, List.map_flatMap, List.map_map, Function.comp_def]
    apply List.flatMap_congr
    intro p hp
    have hpE : p ∈ insert v U := by simpa using hp
    apply List.map_congr_left
    intro q hq
    have hqE : q ∈ (insert v U).erase p := by simpa using hq
    have hr := product_double_erase_ratio (pathVacuumBase t b L Y) (insert v U) p q hpE hqE hbase
    have hpT : p ∉ ((insert v U).erase p).erase q := fun hh =>
      Finset.notMem_erase p _ (Finset.mem_of_mem_erase hh)
    have hc := double_path_coefficient t b L Y (((insert v U).erase p).erase q) S p q v hY
      (((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans hE)
      (hE hpE) (hE (Finset.mem_of_mem_erase hqE)) hpT (Finset.notMem_erase _ _) hreg
      (ha q (hE (Finset.mem_of_mem_erase hqE))) hShell
    congr 1
    change _ = ((∏ x ∈ insert v U, pathVacuumBase t b L Y x)/
      (∏ x ∈ ((insert v U).erase p).erase q, pathVacuumBase t b L Y x))*_
    rw [hr]
    exact hc.symm

theorem correctionEntryTerms_support (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (e : RowEntry) (v : ℂ) (U : Finset ℂ) (z : ℂ × Finset ℂ)
    (hz : z ∈ correctionEntryTerms t b L Y e v U) : z.2 ⊆ insert v U := by
  classical
  cases e <;> simp only [correctionEntryTerms] at hz
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    exact Finset.erase_subset _ _
  · simp only [List.mem_singleton] at hz
    subst z
    exact Finset.Subset.refl _
  · obtain ⟨p,hp,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hz
    exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    exact Finset.erase_subset _ _

noncomputable def correctionWordTerms (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ) :
    List (RowEntry × ℂ) → Finset ℂ → List (ℂ × Finset ℂ)
  | [], U => [(1,U)]
  | (e,v)::w, U => (correctionEntryTerms t b L Y e v U).flatMap
      (fun z => (correctionWordTerms t b L Y w z.2).map (fun y => (z.1*y.1,y.2)))

theorem vacuumPotential_ne_zero (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y S U : Finset ℂ)
    (hY : Y ⊆ S) (hU : U ⊆ S) (hreg : BetheRegular t S)
    (ha : ∀ p ∈ S, vacuumA t b p L ≠ 0) : vacuumPotential t b L Y U ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp =>
    pathVacuumBase_ne_zero t b L Y S hY p (hU hp) hreg (ha p (hU hp)))

theorem correctionWordTerms_support (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (w : List (RowEntry × ℂ)) (U : Finset ℂ) (z : ℂ × Finset ℂ)
    (hz : z ∈ correctionWordTerms t b L Y w U) : z.2 ⊆ U ∪ (w.map Prod.snd).toFinset := by
  classical
  induction w generalizing U z with
  | nil =>
    simp only [correctionWordTerms, List.mem_singleton] at hz
    subst z
    simp
  | cons a w ih =>
    rcases a with ⟨e,v⟩
    obtain ⟨y, hy, hrest⟩ := List.mem_flatMap.mp hz
    obtain ⟨q, hq, heq⟩ := List.mem_map.mp hrest
    subst z
    have htail := ih y.2 q hq
    have hstep := correctionEntryTerms_support t b L Y e v U y hy
    intro x hx
    have hh := htail hx
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
    rcases Finset.mem_union.mp hh with h | h
    · rcases Finset.mem_insert.mp (hstep h) with rfl | hu
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hu
    · exact Or.inr (Or.inr h)

noncomputable def addedVacuumProduct (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (w : List (RowEntry × ℂ)) : ℂ := (w.map (fun ev => pathVacuumBase t b L Y ev.2)).prod

/-- Exact telescoping along all ordered paths, with repeated endpoints retained. -/
theorem wordTerms_path_factorization (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y S U : Finset ℂ)
    (hY : Y ⊆ S) (hU : U ⊆ S) (w : List (RowEntry × ℂ))
    (hw : ∀ ev ∈ w, ev.2 ∈ S) (hreg : BetheRegular t S)
    (ha : ∀ p ∈ S, vacuumA t b p L ≠ 0) (hShell : BalancedRoots t b L 0 Y)
    (hfresh : WordRegular t U w) :
    wordTerms t b L w U = (correctionWordTerms t b L Y w U).map
      (fun z => (vacuumPotential t b L Y U * addedVacuumProduct t b L Y w /
        vacuumPotential t b L Y z.2 * z.1,z.2)) := by
  classical
  induction w generalizing U with
  | nil =>
    have hn := vacuumPotential_ne_zero t b L Y S U hY hU hreg ha
    simp [wordTerms, correctionWordTerms, addedVacuumProduct, hn]
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    have hv : v ∈ S := hw (e,v) (by simp)
    have htail : ∀ ev ∈ w, ev.2 ∈ S := fun ev hev => hw ev (by simp [hev])
    rw [wordTerms, entryTerms_path_factorization t b L Y S U hY hU v hv e hreg ha hShell]
    simp only [correctionWordTerms, List.flatMap_map, List.map_flatMap, List.map_map,
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
      rcases Finset.mem_union.mp (correctionWordTerms_support t b L Y w z.2 y hy hx) with h | h
      · exact hzS h
      · obtain ⟨ev,hev,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
        exact heq ▸ htail ev hev
    have hnz := vacuumPotential_ne_zero t b L Y S z.2 hY hzS hreg ha
    have hny := vacuumPotential_ne_zero t b L Y S y.2 hY hyS hreg ha
    have hE : vacuumPotential t b L Y (insert v U) =
        pathVacuumBase t b L Y v * vacuumPotential t b L Y U := by
      exact Finset.prod_insert hfresh.1
    simp only [addedVacuumProduct, List.map_cons, List.prod_cons]
    congr 1
    rw [hE]
    field_simp
    <;> ring

end SixVertex
