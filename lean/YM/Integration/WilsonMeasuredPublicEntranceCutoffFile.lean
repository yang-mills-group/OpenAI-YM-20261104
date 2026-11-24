import YM.Integration.WilsonMovingForkHeterogeneousCut
/-! The original filed family also admits its genuine terminal fibre when the two cutoffs coincide. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCutoffFile
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonSeparatedBranchStencil (Trial bill read)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n → ℕ)
local notation "C" => R.family


open WilsonMovingForkHeterogeneousCut (Filed)
variable {K:ℕ}(file:Filed R d K)
abbrev Electrodes := ℕ → (i:Fin n) → R.family.label (d i) ≃ₗ[ℂ] R.family.label (d i)

private def raw (N per:ℕ)(w:∀i,(C).label (d i))(ξ:Fin n→Site ((C).side K per))(j:ℕ):
    Config G ((C).side j per)→ℂ:=
  if date:j=K then date.symm ▸ (if N=K then product R d (N:=N) ξ w else file.row N per w ξ K)
  else file.row N per w ξ j

def complete (electrode:Electrodes R d):Filed R d K where
  station:=file.station
  target:=file.target
  before:=file.before
  A:=fun N per i=>if N=K then electrode per i else file.A N per i
  arrived:=by
    intro N per live i x
    simpa only [if_neg (Nat.ne_of_gt live)] using file.arrived N per live i x
  row:=raw R d file
  seed:=by
    intro N per live w ξ
    simpa [raw,Nat.ne_of_gt live] using file.seed N per live w ξ

variable (electrode:Electrodes R d)

theorem cutoff (per:ℕ)(w:∀i,(C).label (d i))(ξ:Fin n→Site ((C).side K per)):
    (complete R d file electrode).A K per=electrode per ∧
    (complete R d file electrode).row K per w ξ K=product R d (N:=K) ξ w:=by
  simp [complete,raw]

theorem live {N:ℕ}(later:K<N)(per:ℕ):
    (complete R d file electrode).A N per=file.A N per ∧
    (complete R d file electrode).row N per=file.row N per:=by
  constructor
  · simp [complete,Nat.ne_of_gt later]
  · funext w ξ j
    by_cases same:j=K
    · subst j; simp [complete,raw,Nat.ne_of_gt later]
    · simp [complete,raw,same]

theorem original {N:ℕ}(present:K≤N)(per:ℕ)(w:∀i,(C).label (d i))(ξ:Fin n→Site ((C).side K per)):
    (complete R d file electrode).row N per w ξ K=product R d (N:=N) ξ w:=by
  rcases present.eq_or_lt with rfl|high
  · exact (cutoff R d file electrode per w ξ).2
  · exact (complete R d file electrode).seed N per high w ξ

end YM.Integration.WilsonMeasuredPublicEntranceCutoffFile
end
