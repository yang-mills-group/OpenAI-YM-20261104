import YM.Integration.WilsonMeasuredPublicEntranceProfilePhase
import YM.Integration.WilsonMeasuredPublicEntranceTranslatedProfile
/-! Signed Gibbs corrections of an entire translated profile at the original flat and nonflat readings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
open Function Set Finset Filter MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonMeasuredPublicEntranceProfileRegistry (Billed)
open WilsonMeasuredPublicEntrancePinnedPass (ear)
open PertExtension PertExtension.LatticePT
open Extraction WilsonAddressedPhysicalCells
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u k:ℕ}
local notation "V" j:max => Config G (R.family.side j per)
variable (file:Filed R d K)(fk:f≤K)(cut:K≤N)(road:u≤K)(Y:∀i,R.family.label (d i))
  (turn:Fin n→Motion)(loc:Fin n→Site (R.family.side f per))(s:(Stock.census (Fin n)).Mode)

/-- Both conditional readings use the original normalized Wilson kernels. -/
def difference:ℂ:=
  actualTransport R.family (N:=N) (physical R d (N:=N) Y turn loc s) (road.trans cut) 1-
    actualTransport R.family (N:=N) (submitted R d (N:=N) file fk Y turn loc s) road 1

theorem original:WilsonMeasuredPublicEntranceCellWords.difference R d file fk cut road Y turn loc s=
    difference R d file fk cut road Y turn loc s:=by
  let raw:=physical R d (N:=N) Y turn loc s
  have cont:Continuous raw:=continuous_finsetProd _ fun i _=>R.family.continuousO _ _ _ _ _
  have atN:WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit R.family N per 0 raw K cut) u road=
      actualTransport R.family (N:=N) raw (road.trans cut) 1:=by
    unfold WilsonThermometerUnitFilingCoarse.reading
    rw [WilsonThermometerUnitFilingCoarse.cutoff R cut road raw cont,←WilsonSeparatedOriginalSlabHeldProxy.normalized R (road.trans cut) raw]
    ring
  exact congrArg₂ (·-·) atN (WilsonThermometerUnitFilingPosterior.weighted R (submitted R d (N:=N) file fk Y turn loc s) road)

end YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
end
