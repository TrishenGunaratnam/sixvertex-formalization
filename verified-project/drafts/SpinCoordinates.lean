import SixVertex.PhysicalSectorMinimum
import SixVertex.FreeSlaterPositive
import Mathlib.Data.Finset.Sort

namespace SixVertex
noncomputable section

/-- Read the nested spin word at a concrete site. -/
def rowSpinAt : (L : ℕ) → RowSpins L → Fin L → Fin 2
  | 0,_ => fun i => Fin.elim0 i
  | L+1,q => Fin.cons q.1 (rowSpinAt L q.2)

/-- Reconstruct the nested spin word from its site values. -/
def rowSpinsOfSites : (L : ℕ) → (Fin L → Fin 2) → RowSpins L
  | 0,_ => ()
  | L+1,f => (f 0,rowSpinsOfSites L (fun i => f i.succ))

theorem rowSpinAt_ofSites (L : ℕ) (f : Fin L → Fin 2) :
    rowSpinAt L (rowSpinsOfSites L f)=f := by
  induction L with
  | zero => funext i;exact Fin.elim0 i
  | succ L ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rowSpinAt,rowSpinsOfSites]
    · simpa [rowSpinAt,rowSpinsOfSites] using congrFun (ih (fun j => f j.succ)) j

theorem rowSpinsOfSites_at (L : ℕ) (q : RowSpins L) :
    rowSpinsOfSites L (rowSpinAt L q)=q := by
  induction L with
  | zero => cases q;rfl
  | succ L ih =>
    rcases q with ⟨a,t⟩
    simpa only [rowSpinsOfSites,rowSpinAt,Fin.cons_zero,Fin.cons_succ] using
      congrArg (fun r : RowSpins L => (a,r)) (ih t)

def rowSpinSitesEquiv (L : ℕ) : RowSpins L ≃ (Fin L → Fin 2) where
  toFun := rowSpinAt L
  invFun := rowSpinsOfSites L
  left_inv := rowSpinsOfSites_at L
  right_inv := rowSpinAt_ofSites L

/-- The physical particle count is exactly the sum of the site bits. -/
theorem minusCount_eq_sum_sites (L : ℕ) (q : RowSpins L) :
    minusCount L q=∑ i : Fin L,(rowSpinAt L q i).val := by
  induction L with
  | zero => cases q;simp [minusCount]
  | succ L ih =>
    rcases q with ⟨a,t⟩
    simpa [minusCount,rowSpinAt,Fin.sum_univ_succ] using congrArg (fun k => a.val+k) (ih t)

def occupiedSites (L : ℕ) (q : RowSpins L) : Finset (Fin L) :=
  Finset.univ.filter (fun i => rowSpinAt L q i=1)

theorem occupiedSites_card (L : ℕ) (q : RowSpins L) :
    (occupiedSites L q).card=minusCount L q := by
  classical
  rw [minusCount_eq_sum_sites]
  unfold occupiedSites
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  generalize rowSpinAt L q i=a
  fin_cases a <;> norm_num

/-- Ordered occupied positions of an actual physical sector configuration. -/
def occupiedCoordinates {L particles : ℕ} (q : ParticleConfigurations L particles) : Fin particles → ℤ :=
  fun i => ((occupiedSites L q.val).orderEmbOfFin ((occupiedSites_card L q.val).trans q.property) i).val

theorem occupiedCoordinates_strictMono {L particles : ℕ} (q : ParticleConfigurations L particles) :
    StrictMono (occupiedCoordinates q) := by
  intro i j hij
  have h := ((occupiedSites L q.val).orderEmbOfFin
    ((occupiedSites_card L q.val).trans q.property)).strictMono hij
  change (((occupiedSites L q.val).orderEmbOfFin
    ((occupiedSites_card L q.val).trans q.property) i).val)<
      (((occupiedSites L q.val).orderEmbOfFin
    ((occupiedSites_card L q.val).trans q.property) j).val) at h
  unfold occupiedCoordinates
  exact_mod_cast h

theorem occupiedCoordinates_nonneg {L particles : ℕ} (q : ParticleConfigurations L particles)
    (i : Fin particles) : 0≤occupiedCoordinates q i := by
  unfold occupiedCoordinates
  exact Int.natCast_nonneg _

theorem occupiedCoordinates_lt_length {L particles : ℕ} (q : ParticleConfigurations L particles)
    (i : Fin particles) : occupiedCoordinates q i<(L : ℤ) := by
  unfold occupiedCoordinates
  exact_mod_cast ((occupiedSites L q.val).orderEmbOfFin
    ((occupiedSites_card L q.val).trans q.property) i).isLt

/-- The positive free Slater candidate on the actual physical spin-sector basis.
Its eigenvalue equation for the spin Hamiltonian remains to be proved. -/
def spinFreeSlaterVector {particles : ℕ} (L : ℕ) (Y : Fin particles → ℝ) :
    ParticleConfigurations L particles → ℂ := fun q =>
  freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) (occupiedCoordinates q)/
    freeSlaterPhase particles

theorem spinFreeSlaterVector_positive {particles : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin particles → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (q : ParticleConfigurations L particles) :
    (spinFreeSlaterVector L Y q).im=0 ∧ 0<(spinFreeSlaterVector L Y q).re := by
  exact freeSlaterWave_fixed_phase_positive L hL Y hY (occupiedCoordinates q)
    (occupiedCoordinates_strictMono q) (occupiedCoordinates_nonneg q) (occupiedCoordinates_lt_length q)

theorem spinFreeSlaterVector_ne_zero {particles : ℕ} (L : ℕ) (hL : 0<L)
    (hp : particles≤L) (Y : Fin particles → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0) :
    spinFreeSlaterVector L Y≠0 := by
  obtain ⟨q,hq⟩ := exists_minusCount_eq L particles hp
  have h := (spinFreeSlaterVector_positive L hL Y hY ⟨q,hq⟩).2
  intro he
  rw [he] at h
  simpa using h

end
end SixVertex
