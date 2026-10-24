import SixVertex.ScalarProductWeights
import SixVertex.SlavnovAssumption

/-!
# Lemma 2.4, conditional on the explicitly assumed Slavnov identity

The single external hypothesis is `SlavnovIdentity`, the derivative-over-Cauchy
formula. Source-column normalization, the complex coincident limits, the exact
Gaudin norm and its nonvanishing, arbitrary deleted columns and the weighted
minor identity are proved. No global mathematical axiom is introduced.
-/
namespace SixVertex
open Filter Topology

/-- The paper's displayed quotient on the generic nonzero-Cauchy domain. -/
theorem slavnov_exact {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (hSlavnov : SlavnovIdentity lam b L Y twist)
    (U : Fin n → ℂ) (hreg : ∀ k, SourceRegular lam b L Y (U k))
    (hcross : ∀ j k, Complex.sinh (U k-Y j) ≠ 0) (hC : (scalarCauchy Y U).det ≠ 0) :
    algebraicScalarProduct lam b L Y U =
      (Complex.exp (-((n : ℂ)*Complex.I*twist)) *
        (∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L) *
        (Matrix.of (fun j k => independentRootDerivative lam b L Y twist (U k) j)).det) /
        (scalarCauchy Y U).det :=
  (eq_div_iff hC).mpr (hSlavnov U hreg hcross)

noncomputable def deletedScalarExpression {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (H : Finset (Fin n)) (V : Fin n → ℂ) : ℂ :=
  ((-Complex.sinh (Complex.I*lam))^H.card)⁻¹ *
    ((∏ k ∈ H, extractedVacuum lam b L Y (V k))/(∏ k ∈ H, rootVacuumFactor lam b L Y k)) *
    (((complexGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y twist V).submatrix
      (fun i : H => i.val) (fun j : H => j.val)).det /
    ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det

/-- At arbitrary collisions, the COMPLETE deleted-column expression has the
limit of the actual scalar product. Individual determinant quotients need not
have termwise limits. Repeated limiting roots remain in their original slots. -/
theorem deleted_scalar_coincident_limit {J : Type*} {n : ℕ} (r : Filter J)
    (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (hEven : Even L)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (twist : ℝ) (hShell : OnShell lam b L Y twist)
    (hSlavnov : SlavnovIdentity lam b L Y twist) (hdet : (gaudinMatrix lam b L Y).det ≠ 0)
    (H : Finset (Fin n)) (V : J → Fin n → ℂ) (V₀ : Fin n → ℂ)
    (hV : ∀ k, Tendsto (fun z => V z k) r (𝓝 (V₀ k)))
    (hgeneric : ∀ᶠ z in r,
      (∀ k ∈ H, SourceRegular lam b L Y (V z k)) ∧
      (∀ k ∈ H, ∀ j, Complex.sinh (V z k-Y j) ≠ 0) ∧
      ((scalarCauchy Y (V z)).submatrix (fun i : H => i.val) (fun j : H => j.val)).det ≠ 0) :
    Tendsto (fun z => deletedScalarExpression lam b L Y twist H (V z)) r
      (𝓝 (algebraicScalarProduct lam b L Y (fun k => if k ∈ H then V₀ k else (Y k : ℂ)) /
        algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)))) := by
  classical
  have hSource := slavnov_source_of_identity lam b L Y twist hSlavnov
  have hN := gaudin_norm_ne_zero lam h0 hpi b L hEven Y hY twist hShell hSource hdet
  have ht := (algebraicScalarProduct_tendsto r lam b L Y
    (fun z k => if k ∈ H then V z k else (Y k : ℂ))
    (fun k => if k ∈ H then V₀ k else (Y k : ℂ)) (by
      intro k
      by_cases hk : k ∈ H
      · simpa [hk] using hV k
      · simpa [hk] using (tendsto_const_nhds : Tendsto (fun _ : J => (Y k : ℂ)) r (𝓝 (Y k : ℂ))))).div tendsto_const_nhds hN
  apply ht.congr'
  filter_upwards [hgeneric] with z hz
  exact deleted_scalar_product lam h0 hpi b L hEven Y hY twist hShell hSource hdet H (V z) hz.1 hz.2.1 hz.2.2

structure ExactScalarProducts {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) : Prop where
  slavnov : SlavnovIdentity lam b L Y twist
  source_normalization : ∀ u, SourceRegular lam b L Y u →
    (∀ j, Complex.sinh (u-Y j) ≠ 0) → ∀ j,
    independentRootDerivative lam b L Y twist u j =
      Complex.exp (Complex.I*twist)*extractedVacuum lam b L Y u *
        (-2*(Real.pi : ℂ)*Complex.I)*scalarSource lam b L Y twist u j
  source_gaudin : ∀ k j, Tendsto (fun u => scalarSource lam b L Y twist u j)
    (𝓝[≠] (Y k : ℂ)) (𝓝 (complexGaudin lam b L Y j k))
  norm : algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) =
    gaudinNormPrefactor lam b L Y * (complexGaudin lam b L Y).det
  nonzero_norm : (gaudinMatrix lam b L Y).det ≠ 0 →
    algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) ≠ 0
  deleted : (gaudinMatrix lam b L Y).det ≠ 0 →
    ∀ (H : Finset (Fin n)) (V : Fin n → ℂ),
    (∀ k ∈ H, SourceRegular lam b L Y (V k)) →
    (∀ k ∈ H, ∀ j, Complex.sinh (V k-Y j) ≠ 0) →
    ((scalarCauchy Y V).submatrix (fun i : H => i.val) (fun j : H => j.val)).det ≠ 0 →
    algebraicScalarProduct lam b L Y (fun k => if k ∈ H then V k else (Y k : ℂ)) /
      algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ)) =
      deletedScalarExpression lam b L Y twist H V
  weighted : (gaudinMatrix lam b L Y).det ≠ 0 →
    (∀ j, 0 < countingSlope lam b L Y (Y j)) → ∀ (H : Finset (Fin n)) (V : Fin n → ℂ),
    (((complexGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y twist V).submatrix
      (fun i : H => i.val) (fun j : H => j.val)).det =
      (∏ i : H, gaudinEll lam b L Y i.val) *
      (((weightedGaudin lam b L Y)⁻¹ * scalarSourceMatrix lam b L Y twist V).submatrix
        (fun i : H => i.val) (fun j : H => j.val)).det
  coincident : ∀ (J : Type) (r : Filter J) (hdet : (gaudinMatrix lam b L Y).det ≠ 0)
    (H : Finset (Fin n)) (V : J → Fin n → ℂ) (V₀ : Fin n → ℂ),
    (∀ k, Tendsto (fun z => V z k) r (𝓝 (V₀ k))) →
    (∀ᶠ z in r, (∀ k ∈ H, SourceRegular lam b L Y (V z k)) ∧
      (∀ k ∈ H, ∀ j, Complex.sinh (V z k-Y j) ≠ 0) ∧
      ((scalarCauchy Y (V z)).submatrix (fun i : H => i.val) (fun j : H => j.val)).det ≠ 0) →
    Tendsto (fun z => deletedScalarExpression lam b L Y twist H (V z)) r
      (𝓝 (algebraicScalarProduct lam b L Y (fun k => if k ∈ H then V₀ k else (Y k : ℂ)) /
        algebraicScalarProduct lam b L Y (fun k => (Y k : ℂ))))

/-- Lemma 2.4: all consequences verified, relative to the one explicitly
assumed external Slavnov identity. The assumed list records this boundary. -/
theorem exact_scalar_products_and_deleted_columns {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (hL : 4 ≤ L) (hEven : Even L)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (twist : ℝ)
    (hShell : OnShell lam b L Y twist) (hSlavnov : SlavnovIdentity lam b L Y twist) :
    ExactScalarProducts lam b L Y twist := by
  have hSource := slavnov_source_of_identity lam b L Y twist hSlavnov
  refine ⟨hSlavnov, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun u hu hc j => independentRootDerivative_source lam b L Y twist u hu hc j
  · exact scalarSource_gaudin_limit lam h0 hpi b L hEven Y hY twist hShell
  · exact gaudin_norm_exact lam h0 hpi b L hEven Y hY twist hShell hSource
  · exact gaudin_norm_ne_zero lam h0 hpi b L hEven Y hY twist hShell hSource
  · exact fun hd H V hv hc hdC => deleted_scalar_product lam h0 hpi b L hEven Y hY twist hShell hSource hd H V hv hc hdC
  · exact fun hd hp H V => weighted_source_minor lam b L Y twist hd hp H V
  · exact fun J r hd H V V₀ hv hg => deleted_scalar_coincident_limit r lam h0 hpi b L hEven Y hY twist hShell hSlavnov hd H V V₀ hv hg

end SixVertex
