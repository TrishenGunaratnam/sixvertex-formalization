import SixVertex.NormalizedWords

namespace SixVertex

theorem correctionEntryTerms_card_charge (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (e : RowEntry) (v : ℂ) (U : Finset ℂ) (hv : v ∉ U) (z : ℂ × Finset ℂ)
    (hz : z ∈ correctionEntryTerms t b L Y e v U) :
    (z.2.card : ℤ) = (U.card : ℤ)+entryCharge e := by
  classical
  have hE : (insert v U).card = U.card+1 := Finset.card_insert_of_notMem hv
  cases e <;> simp only [correctionEntryTerms] at hz
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    have hpE : p ∈ insert v U := by simpa using hp
    rw [Finset.card_erase_of_mem hpE,hE]
    simp [entryCharge]
  · simp only [List.mem_singleton] at hz
    subst z
    simp [hE,entryCharge]
  · obtain ⟨p,hp,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have hpE : p ∈ insert v U := by simpa using hp
    have hqE : q ∈ (insert v U).erase p := by simpa using hq
    have hnonempty : 0 < ((insert v U).erase p).card := Finset.card_pos.mpr ⟨q,hqE⟩
    rw [Finset.card_erase_of_mem hqE,Finset.card_erase_of_mem hpE,hE]
    simp only [Finset.card_erase_of_mem hpE,hE, Nat.add_sub_cancel] at hnonempty
    simp only [Nat.add_sub_cancel, entryCharge]
    omega
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    have hpE : p ∈ insert v U := by simpa using hp
    rw [Finset.card_erase_of_mem hpE,hE]
    simp [entryCharge]

theorem decoratedCorrectionWords_card_charge (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y : Finset ℂ)
    (eta : Finset ℂ → RowEntry → ℂ → ℂ) (w : List (RowEntry × ℂ))
    (U : Finset ℂ) (hreg : WordRegular t U w) (z : ℂ × Finset ℂ)
    (hz : z ∈ decoratedCorrectionWords t b L Y eta w U) :
    (z.2.card : ℤ) = (U.card : ℤ)+(w.map (fun ev => entryCharge ev.1)).sum := by
  induction w generalizing U z with
  | nil =>
    simp only [decoratedCorrectionWords,List.mem_singleton] at hz
    subst z
    simp
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    obtain ⟨y,hy,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have hc := correctionEntryTerms_card_charge t b L Y e v U hreg.1 y hy
    have hs := correctionEntryTerms_support t b L Y e v U y hy
    have ht := ih y.2 (hreg.2.2.mono hs w) q hq
    simpa only [List.map_cons,List.sum_cons,Prod.fst, hc,add_assoc] using ht

theorem relativeCorrection_path_cardinality {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) (z : ℂ × Finset ℂ)
    (hz : z ∈ relativeCorrectionWords lam b L Y w (rootSet Y)) (hcard : z.2.card = (rootSet Y).card) :
    ((rootSet Y) \ z.2).card = (z.2 \ rootSet Y).card ∧ (z.2 \ rootSet Y).card ≤ w.length := by
  have hs := decoratedCorrectionWords_support (Complex.I*lam) (fun j => (b j : ℂ)) L
    (rootSet Y) _ w (rootSet Y) z hz
  have hsub : z.2 \ rootSet Y ⊆ (w.map Prod.snd).toFinset := by
    intro x hx
    exact (Finset.mem_union.mp (hs (Finset.mem_sdiff.mp hx).1)).resolve_left (Finset.mem_sdiff.mp hx).2
  have ha := Finset.card_sdiff_add_card_inter (rootSet Y) z.2
  have hb := Finset.card_sdiff_add_card_inter z.2 (rootSet Y)
  rw [Finset.inter_comm z.2 (rootSet Y)] at hb
  have hc := Finset.card_le_card hsub
  have hd := (w.map Prod.snd).toFinset_card_le
  simp only [List.length_map] at hd
  exact ⟨by omega,hc.trans hd⟩

/-- In a diagonal entry word every input sector equals the original one,
so every relative parity is one, path by path. -/
theorem diagonal_relative_corrections {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ)) (U : Finset ℂ) (hU : U.card = n)
    (hreg : WordRegular (Complex.I*lam) U w)
    (hdiag : ∀ ev ∈ w, ev.1 = .A ∨ ev.1 = .L) :
    relativeCorrectionWords lam b L Y w U =
      correctionWordTerms (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) w U := by
  classical
  induction w generalizing U with
  | nil => rfl
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    have he := hdiag (e,v) (by simp)
    have hecharge : entryCharge e = 0 := by rcases he with rfl | rfl <;> rfl
    have htail : ∀ ev ∈ w, ev.1 = .A ∨ ev.1 = .L := fun ev hev => hdiag ev (by simp [hev])
    change (correctionEntryTerms _ _ _ _ e v U).flatMap _ = _
    rw [correctionWordTerms]
    apply List.flatMap_congr
    intro z hz
    have hc := correctionEntryTerms_card_charge (Complex.I*lam) (fun j => (b j : ℂ)) L
      (rootSet Y) e v U hreg.1 z hz
    have hzcard : z.2.card = n := by rw [hecharge,hU] at hc; omega
    have hs := correctionEntryTerms_support (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) e v U z hz
    change (relativeCorrectionWords lam b L Y w z.2).map _ = _
    rw [ih z.2 hzcard (hreg.2.2.mono hs w) htail]
    simp [hU]

end SixVertex
