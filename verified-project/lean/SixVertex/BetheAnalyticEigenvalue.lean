import SixVertex.BetheEigenvectors

namespace SixVertex

open Filter Topology

/-- The generic spectral domain is open around each of its points. -/
theorem regular_spectral_eventually (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (U : Finset ℂ) (x₀ : ℂ) (hx₀ : x₀ ∉ U) (hreg : BetheRegular t (insert x₀ U)) :
    ∀ᶠ x in 𝓝 x₀, x ∉ U ∧ BetheRegular t (insert x U) := by
  classical
  have hnear : ∀ᶠ x in 𝓝 x₀, ∀ p : {p // p ∈ U},
      Complex.sinh (x-p) ≠ 0 ∧ Complex.sinh ((p : ℂ)-x) ≠ 0 ∧
      Complex.sinh (x-p+t) ≠ 0 ∧ Complex.sinh ((p : ℂ)-x+t) ≠ 0 := by
    rw [Filter.eventually_all]
    intro p
    have hxp : x₀ ≠ (p : ℂ) := fun he => hx₀ (he.symm ▸ p.2)
    have hp : (p : ℂ) ∈ insert x₀ U := Finset.mem_insert_of_mem p.2
    have hx := Finset.mem_insert_self x₀ U
    have h1 := (Complex.continuous_sinh.comp (continuous_id.sub continuous_const)).continuousAt.eventually_ne
      (hreg.1 x₀ hx p hp hxp)
    have h2 := (Complex.continuous_sinh.comp (continuous_const.sub continuous_id)).continuousAt.eventually_ne
      (hreg.1 p hp x₀ hx hxp.symm)
    have h3 := (Complex.continuous_sinh.comp ((continuous_id.sub continuous_const).add continuous_const)).continuousAt.eventually_ne
      (hreg.2 x₀ hx p hp)
    have h4 := (Complex.continuous_sinh.comp ((continuous_const.sub continuous_id).add continuous_const)).continuousAt.eventually_ne
      (hreg.2 p hp x₀ hx)
    exact h1.and (h2.and (h3.and h4))
  have hU := hreg.mono (Finset.subset_insert x₀ U)
  filter_upwards [hnear] with x hx
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    have h := (hx ⟨x,hmem⟩).1
    simp at h
  · intro p hpE q hqE hn
    rcases Finset.mem_insert.mp hpE with hp | hpU
    · subst p
      rcases Finset.mem_insert.mp hqE with hq | hqU
      · subst q
        exact False.elim (hn rfl)
      · exact (hx ⟨q,hqU⟩).1
    · rcases Finset.mem_insert.mp hqE with hq | hqU
      · subst q
        exact (hx ⟨p,hpU⟩).2.1
      · exact hU.1 p hpU q hqU hn
  · intro p hpE q hqE
    rcases Finset.mem_insert.mp hpE with hp | hpU
    · subst p
      rcases Finset.mem_insert.mp hqE with hq | hqU
      · subst q
        simpa using ht
      · exact (hx ⟨q,hqU⟩).2.2.1
    · rcases Finset.mem_insert.mp hqE with hq | hqU
      · subst q
        exact (hx ⟨p,hpU⟩).2.2.2
      · exact hU.2 p hpU q hqU

theorem twistedStandardRow_analytic (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (twist : ℝ)
    (q r : RowSpins L) (z : ℂ) :
    AnalyticAt ℂ (fun x => twistedStandardRow t b L twist x q r) z := by
  simp only [twistedStandardRow, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact (analyticAt_const.mul (betheBlock_analytic t b L 0 0 q r z)).add
    (analyticAt_const.mul (betheBlock_analytic t b L 1 1 q r z))

theorem twisted_row_state_analytic (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (twist : ℝ)
    (M : Matrix (RowSpins L) (RowSpins L) ℂ) (q r : RowSpins L) (z : ℂ) :
    AnalyticAt ℂ (fun x => (twistedStandardRow t b L twist x * M) q r) z := by
  simp only [Matrix.mul_apply]
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (twistedStandardRow_analytic t b L twist q k z).mul analyticAt_const

/-- The Bethe eigenvalue has an entire extension. The proof uses a nonzero
state component and the complex identity theorem; removable poles are
therefore proved rather than interpreted as Lean's value of division by zero. -/
theorem balancedRoots_entire_eigenvalue (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (L : ℕ) (twist : ℝ) (U : Finset ℂ)
    (hU : BalancedRoots t b L twist U) (hM : betheState t ht b L U ≠ 0)
    (x₀ : ℂ) (hx₀ : x₀ ∉ U) (hreg₀ : BetheRegular t (insert x₀ U)) :
    ∃ ρ : ℂ → ℂ, (∀ z, AnalyticAt ℂ ρ z) ∧
      (∀ x, twistedStandardRow t b L twist x * betheState t ht b L U =
        ρ x • betheState t ht b L U) ∧
      ∀ x, x ∉ U → BetheRegular t (insert x U) → ρ x = abaEigenvalue t b L twist U x := by
  classical
  obtain ⟨q₀,r₀,hm⟩ : ∃ q r, betheState t ht b L U q r ≠ 0 := by
    by_contra hn
    apply hM
    ext q r
    simpa using not_exists.mp (not_exists.mp hn q) r
  let M := betheState t ht b L U
  let ρ : ℂ → ℂ := fun x => (twistedStandardRow t b L twist x * M) q₀ r₀ / M q₀ r₀
  have hρ : ∀ z, AnalyticAt ℂ ρ z := fun z =>
    (twisted_row_state_analytic t b L twist M q₀ r₀ z).div_const
  have hgen : ∀ x, x ∉ U → BetheRegular t (insert x U) →
      ρ x = abaEigenvalue t b L twist U x := by
    intro x hx hr
    have h := congrArg (fun N : Matrix (RowSpins L) (RowSpins L) ℂ => N q₀ r₀)
      (balancedRoots_eigenvector t ht b L twist U hU x hx hr)
    change (twistedStandardRow t b L twist x * M) q₀ r₀ =
      abaEigenvalue t b L twist U x * M q₀ r₀ at h
    dsimp [ρ]
    rw [h, mul_div_cancel_right₀ _ hm]
  have heigen : ∀ x, twistedStandardRow t b L twist x * M = ρ x • M := by
    intro x
    ext q r
    have hf : (fun x : ℂ => (twistedStandardRow t b L twist x * M) q r) =
        (fun x : ℂ => ρ x * M q r) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := x₀)
      · intro z hz
        exact twisted_row_state_analytic t b L twist M q r z
      · intro z hz
        exact (hρ z).mul analyticAt_const
      · filter_upwards [regular_spectral_eventually t ht U x₀ hx₀ hreg₀] with z hz
        rw [hgen z hz.1 hz.2]
        exact congrArg (fun N : Matrix (RowSpins L) (RowSpins L) ℂ => N q r)
          (balancedRoots_eigenvector t ht b L twist U hU z hz.1 hz.2)
    exact congrFun hf x
  exact ⟨ρ,hρ,heigen,hgen⟩

end SixVertex
