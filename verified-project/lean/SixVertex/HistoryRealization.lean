import SixVertex.RemovalBookkeeping

namespace SixVertex

noncomputable def RemovalEvent.relativeParity (n : ℕ) (U : Finset ℂ) : RemovalEvent → ℂ
  | .insert _ => (-1 : ℂ)^U.card/(-1 : ℂ)^n
  | .upper _ _ | .lower _ _ => 1

theorem historyEndpoint_append (U : Finset ℂ) (h g : List RemovalEvent) :
    historyEndpoint U (h++g) = historyEndpoint (historyEndpoint U h) g := by
  induction h generalizing U with
  | nil => rfl
  | cons e h ih => exact ih (e.next U)

theorem historyProduct_append (f : Finset ℂ → RemovalEvent → ℂ) (U : Finset ℂ)
    (h g : List RemovalEvent) :
    historyProduct f U (h++g) = historyProduct f U h * historyProduct f (historyEndpoint U h) g := by
  induction h generalizing U with
  | nil => simp [historyProduct,historyEndpoint]
  | cons e h ih => simp [historyProduct,historyEndpoint,ih,mul_assoc]

theorem RemovalHistory.Valid.append (Y U : Finset ℂ) (h g : List RemovalEvent)
    (hh : RemovalHistory.Valid Y U h) (hg : RemovalHistory.Valid Y (historyEndpoint U h) g) :
    RemovalHistory.Valid Y U (h++g) := by
  induction h generalizing U with
  | nil => exact hg
  | cons e h ih => exact ⟨hh.1,ih (e.next U) hh.2 hg⟩

theorem correctionEntry_history_exists (t : ℂ) (b : ℕ → ℂ) (L n : ℕ) (Y S U : Finset ℂ)
    (hY : Y ⊆ S) (hU : U ⊆ S) (v : ℂ) (hvS : v ∈ S) (hvY : v ∉ Y) (hvU : v ∉ U)
    (hreg : BetheRegular t S) (e : RowEntry) (z : ℂ × Finset ℂ)
    (hz : z ∈ correctionEntryTerms t b L Y e v U) :
    ∃ h : List RemovalEvent, RemovalHistory.Valid Y U h ∧ historyEndpoint U h = z.2 ∧
      historyProduct (fun V e => e.relativeParity n V) U h *
        historyProduct (fun V e => e.gamma t b L Y V) U h =
          ((-1 : ℂ)^U.card/(-1 : ℂ)^n)*z.1 := by
  classical
  cases e <;> simp only [correctionEntryTerms] at hz
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    have hpE : p ∈ insert v U := by simpa using hp
    refine ⟨[.insert v,.upper v p],⟨⟨hvY,hvU⟩,hpE,trivial⟩,rfl,?_⟩
    simp [historyProduct,RemovalEvent.relativeParity,RemovalEvent.gamma,RemovalEvent.next]
  · simp only [List.mem_singleton] at hz
    subst z
    refine ⟨[.insert v],⟨⟨hvY,hvU⟩,trivial⟩,rfl,?_⟩
    simp [historyProduct,RemovalEvent.relativeParity,RemovalEvent.gamma]
  · obtain ⟨p,hp,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have hpE : p ∈ insert v U := by simpa using hp
    have hqE : q ∈ (insert v U).erase p := by simpa using hq
    refine ⟨[.insert v,.upper v p,.lower v q],⟨⟨hvY,hvU⟩,hpE,hqE,trivial⟩,rfl,?_⟩
    simp only [historyProduct,RemovalEvent.relativeParity,RemovalEvent.gamma,RemovalEvent.next,
      mul_one,one_mul]
    rw [doublePathCorrection_sequential t b L Y (insert v U) S p q v hY
      (Finset.insert_subset hvS hU) hpE hqE hreg]
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    have hpE : p ∈ insert v U := by simpa using hp
    refine ⟨[.insert v,.lower v p],⟨⟨hvY,hvU⟩,hpE,trivial⟩,rfl,?_⟩
    simp [historyProduct,RemovalEvent.relativeParity,RemovalEvent.gamma,RemovalEvent.next]

/-- Every path in the actual normalized entry-word expansion has a valid
ordered removal history with precisely the same gamma and parity weight. -/
theorem relativeCorrection_history_exists {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (S U : Finset ℂ) (hY : rootSet Y ⊆ S) (hU : U ⊆ S)
    (w : List (RowEntry × ℂ)) (hw : ∀ ev ∈ w, ev.2 ∈ S ∧ ev.2 ∉ rootSet Y)
    (hreg : BetheRegular (Complex.I*lam) S) (hfresh : WordRegular (Complex.I*lam) U w)
    (z : ℂ × Finset ℂ) (hz : z ∈ relativeCorrectionWords lam b L Y w U) :
    ∃ h : List RemovalEvent, RemovalHistory.Valid (rootSet Y) U h ∧ historyEndpoint U h = z.2 ∧
      z.1 = historyProduct (fun V e => e.relativeParity n V) U h *
        historyProduct (fun V e => e.gamma (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) V) U h := by
  induction w generalizing U z with
  | nil =>
    simp only [relativeCorrectionWords,decoratedCorrectionWords,List.mem_singleton] at hz
    subst z
    exact ⟨[],trivial,rfl,by simp [historyProduct]⟩
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    obtain ⟨y,hy,hr⟩ := List.mem_flatMap.mp hz
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    have hv := hw (e,v) (by simp)
    obtain ⟨h,hh,he,hweight⟩ := correctionEntry_history_exists (Complex.I*lam) (fun j => (b j : ℂ))
      L n (rootSet Y) S U hY hU v hv.1 hv.2 hfresh.1 hreg e y hy
    have hs := correctionEntryTerms_support (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) e v U y hy
    have hyS : y.2 ⊆ S := hs.trans (Finset.insert_subset hv.1 hU)
    have hwtail : ∀ ev ∈ w, ev.2 ∈ S ∧ ev.2 ∉ rootSet Y := fun ev hev => hw ev (by simp [hev])
    obtain ⟨g,hg,ge,gweight⟩ := ih y.2 hyS hwtail (hfresh.2.2.mono hs w) q hq
    refine ⟨h++g,RemovalHistory.Valid.append _ _ h g hh (by simpa only [he] using hg),?_,?_⟩
    · rw [historyEndpoint_append,he,ge]
    · simp only [historyProduct_append,he]
      rw [gweight]
      calc
        _ = (historyProduct (fun V e => e.relativeParity n V) U h *
            historyProduct (fun V e => e.gamma (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) V) U h) *
          (historyProduct (fun V e => e.relativeParity n V) y.2 g *
            historyProduct (fun V e => e.gamma (Complex.I*lam) (fun j => (b j : ℂ)) L (rootSet Y) V) y.2 g) := by
          rw [hweight]
        _ = _ := by ring

end SixVertex
