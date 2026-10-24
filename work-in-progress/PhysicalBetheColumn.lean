import SixVertex.HilbertSectors
import SixVertex.FreeSectorHopping
import SixVertex.GaudinPositivity

namespace SixVertex
noncomputable section

/-- The finite-set ABA eigenmatrix and the actual ordered-list Hilbert
Bethe vector have exactly the same physical vacuum column. -/
theorem physicalBetheVector_eq_betheState_column {particles : ℕ}
    (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin particles → ℝ) (hY : Function.Injective Y) (q : RowSpins L) :
    physicalBetheVector lam b L Y q=
      (quantumGauge L*betheState (Complex.I*(lam : ℂ))
        (physical_deformation_ne_zero lam h0 hpi) (fun j => (b j : ℂ)) L (rootSet Y)) q (plusSpins L) := by
  classical
  let U := (List.finRange particles).map (fun j => (Y j : ℂ))
  have hU : U.Nodup := (List.nodup_finRange particles).map (fun i j hij => hY (Complex.ofReal_inj.mp hij))
  have hset : U.toFinset=rootSet Y := by
    ext x
    simp [U,rootSet]
  have h := betheListState_eq_finset (Complex.I*(lam : ℂ))
    (physical_deformation_ne_zero lam h0 hpi) (fun j => (b j : ℂ)) L U hU
  rw [hset] at h
  rw [← h]
  change (quantumGauge L*creationList lam b L U) q (plusSpins L)=_
  rw [betheListState,← Matrix.mul_assoc,mul_vacuumProjector]
  simp only [ite_true,creationList]

theorem betheState_ne_zero_of_physicalBetheVector {particles : ℕ}
    (lam : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin particles → ℝ) (hY : Function.Injective Y)
    (hV : physicalBetheVector lam b L Y≠0) :
    betheState (Complex.I*(lam : ℂ)) (physical_deformation_ne_zero lam h0 hpi)
      (fun j => (b j : ℂ)) L (rootSet Y)≠0 := by
  intro h
  apply hV
  ext q
  rw [physicalBetheVector_eq_betheState_column lam h0 hpi b L Y hY,h,mul_zero]
  rfl

theorem physicalBetheVector_sector {particles : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin particles → ℝ) : SpinSector L (particles : ℤ) (physicalBetheVector lam b L Y) := by
  simpa only [physicalBetheVector,List.length_map,List.length_finRange] using
    physicalListVector_sector lam b L ((List.finRange particles).map (fun j => (Y j : ℂ)))

/-- Restriction to the exact sector and extension by zero recover the
original vector, not merely its projection. -/
theorem physicalSectorExtension_restriction_eq {L particles : ℕ} (v : RowSpins L → ℂ)
    (hv : SpinSector L (particles : ℤ) v) :
    physicalSectorExtension (fun q : ParticleConfigurations L particles => v q.val)=v := by
  funext q
  by_cases hq : minusCount L q=particles
  · simp [physicalSectorExtension,hq]
  · simp [physicalSectorExtension,hq,hv q (by omega)]

theorem physical_sector_restriction_ne_zero {L particles : ℕ} (v : RowSpins L → ℂ)
    (hv : SpinSector L (particles : ℤ) v) (hne : v≠0) :
    (fun q : ParticleConfigurations L particles => v q.val)≠0 := by
  intro hz
  apply hne
  rw [← physicalSectorExtension_restriction_eq v hv,hz]
  funext q
  simp [physicalSectorExtension]

end
end SixVertex
