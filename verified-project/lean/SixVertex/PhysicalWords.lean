import SixVertex.HilbertSectors
import SixVertex.BethePathNormalization

namespace SixVertex

/-- Entries of the original physical monodromy, before normalization. -/
noncomputable def physicalEntry (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (e : RowEntry) (x : ℂ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  match e with
  | .A => rowBlock (fun j => physicalTile lam (b j) x) L 0 0
  | .B => rowBlock (fun j => physicalTile lam (b j) x) L 0 1
  | .C => rowBlock (fun j => physicalTile lam (b j) x) L 1 0
  | .L => rowBlock (fun j => physicalTile lam (b j) x) L 1 1

theorem physicalEntry_gauge (lam : ℝ) (b : ℕ → ℝ) (k : ℕ) (e : RowEntry) (x : ℂ) :
    physicalEntry lam b (2*k) e x = quantumGauge (2*k) *
      entryOperator (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) e x *
      quantumGauge (2*k) * quantumParity (2*k) := by
  cases e <;> exact physical_block_gauge lam b k x _ _

theorem physicalEntry_sector (lam : ℝ) (b : ℕ → ℝ) (k : ℕ) (e : RowEntry)
    (x : ℂ) (s : ℤ) (v : RowSpins (2*k) → ℂ) (hv : SpinSector (2*k) s v) :
    SpinSector (2*k) (s+entryCharge e) ((physicalEntry lam b (2*k) e x).mulVec v) := by
  have hQ := diagonal_mulVec_sector (2*k) s (fun q => evenSign (2*k) q * oddSign (2*k) q) v hv
  have hP := diagonal_mulVec_sector (2*k) s (evenSign (2*k)) _ hQ
  have hE := entryOperator_sector (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) e x s _ hP
  have hP' := diagonal_mulVec_sector (2*k) (s+entryCharge e) (evenSign (2*k)) _ hE
  simpa only [physicalEntry_gauge, quantumGauge, quantumParity, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hP'

noncomputable def physicalWordOperator (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) :
    List (RowEntry × ℂ) → Matrix (RowSpins L) (RowSpins L) ℂ
  | [] => 1
  | (e,x)::w => physicalWordOperator lam b L w * physicalEntry lam b L e x

theorem physicalWordOperator_sector (lam : ℝ) (b : ℕ → ℝ) (k : ℕ)
    (w : List (RowEntry × ℂ)) (s : ℤ) (v : RowSpins (2*k) → ℂ) (hv : SpinSector (2*k) s v) :
    SpinSector (2*k) (s+(w.map (fun ev => entryCharge ev.1)).sum)
      ((physicalWordOperator lam b (2*k) w).mulVec v) := by
  induction w generalizing s v with
  | nil => simpa [physicalWordOperator] using hv
  | cons ev w ih =>
    rcases ev with ⟨e,x⟩
    have h := ih (s+entryCharge e) ((physicalEntry lam b (2*k) e x).mulVec v)
      (physicalEntry_sector lam b k e x s v hv)
    simpa [physicalWordOperator, Matrix.mulVec_mulVec, add_assoc] using h

/-- Every word of nonzero net charge has zero physical expectation. -/
theorem physicalWord_expectation_zero (lam : ℝ) (b : ℕ → ℝ) (k : ℕ)
    (U : List ℂ) (w : List (RowEntry × ℂ))
    (h : (w.map (fun ev => entryCharge ev.1)).sum ≠ 0) :
    inner ℂ (physicalListVector lam b (2*k) U)
      (hilbertMatrixAction (2*k) (physicalWordOperator lam b (2*k) w)
        (physicalListVector lam b (2*k) U)) = 0 := by
  exact spinSector_inner_zero (2*k) U.length
    (U.length+(w.map (fun ev => entryCharge ev.1)).sum) _ _
    (physicalListVector_sector lam b (2*k) U)
    (physicalWordOperator_sector lam b k w U.length _ (physicalListVector_sector lam b (2*k) U))
    (by omega)

/-- The parity sign at each physical action is determined by its input root set. -/
theorem physicalEntry_bethe_action (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (k : ℕ) (e : RowEntry) (x : ℂ) (U : Finset ℂ) :
    physicalEntry lam b (2*k) e x *
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U) =
      (-1 : ℂ)^U.card • (quantumGauge (2*k) *
        (entryOperator (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) e x *
          betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U)) := by
  rw [physicalEntry_gauge]
  calc
    _ = quantumGauge (2*k) * entryOperator (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) e x *
        (quantumGauge (2*k) * quantumParity (2*k) * quantumGauge (2*k)) *
        betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U := by noncomm_ring
    _ = _ := by
      rw [quantumGauge_parity_sandwich]
      simp only [mul_assoc]
      rw [betheState_parity, mul_smul_comm, mul_smul_comm]

noncomputable def physicalWordTerms (t : ℂ) (b : ℕ → ℂ) (L : ℕ) :
    List (RowEntry × ℂ) → Finset ℂ → List (ℂ × Finset ℂ)
  | [], U => [(1,U)]
  | (e,v)::w, U => (entryTerms t b L e v U).flatMap
      (fun z => (physicalWordTerms t b L w z.2).map
        (fun y => ((-1 : ℂ)^U.card*z.1*y.1,y.2)))

theorem physical_word_expansion (lam : ℝ) (ht : Complex.sinh (Complex.I*lam) ≠ 0)
    (b : ℕ → ℝ) (k : ℕ) (w : List (RowEntry × ℂ)) (U : Finset ℂ)
    (hreg : WordRegular (Complex.I*lam) U w) :
    physicalWordOperator lam b (2*k) w *
      (quantumGauge (2*k) * betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) U) =
      weightedEval (fun V => quantumGauge (2*k) *
        betheState (Complex.I*lam) ht (fun j => (b j : ℂ)) (2*k) V)
        (physicalWordTerms (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) w U) := by
  induction w generalizing U with
  | nil => simp [physicalWordOperator, physicalWordTerms, weightedEval]
  | cons ev w ih =>
    rcases ev with ⟨e,v⟩
    rw [physicalWordOperator, mul_assoc, physicalEntry_bethe_action,
      mul_smul_comm, entry_expansion _ ht _ _ e v U hreg.1 hreg.2.1,
      weightedEval_mul_left, weightedEval_mul_left]
    rw [physicalWordTerms]
    have hmap : (entryTerms (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) e v U).flatMap
        (fun z => (physicalWordTerms (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) w z.2).map
          (fun y => ((-1 : ℂ)^U.card*z.1*y.1,y.2))) =
        ((entryTerms (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) e v U).map
          (fun z => ((-1 : ℂ)^U.card*z.1,z.2))).flatMap
        (fun z => (physicalWordTerms (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) w z.2).map
          (fun y => (z.1*y.1,y.2))) := by rw [List.flatMap_map]
    rw [hmap, weightedEval_bind, weightedEval_scale]
    congr 1
    apply weightedEval_congr
    intro z hz
    exact ih z.2 (hreg.2.2.mono (entryTerms_support _ _ _ e v U z hz) w)

end SixVertex
