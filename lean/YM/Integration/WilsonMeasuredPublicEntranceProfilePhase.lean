import YM.Integration.WilsonMeasuredPublicEntrancePinnedPass
import YM.Integration.WilsonMeasuredPublicEntranceTranslatedProfile
/-! Signed Gibbs corrections of an entire translated profile at the original flat and nonflat readings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceProfilePhase
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
variable (file:Filed R d K)(fk:f≤K)(cut:K≤N)(road:u≤K)
  (Y:∀i,R.family.label (d i))(turn:(Fin k→Site (R.family.side f per))→Fin n→Motion)(place:(Fin k→Site (R.family.side f per))→Fin n→Site (R.family.side f per))
  (s:(Stock.census (Fin n)).Mode)
theorem original (φ:Test k)(scale fare:ℝ)
    (_sold:Billed φ (R.family.S.a f) scale (R.family.side f per) (fun cell=>(WilsonMeasuredPublicEntranceCellWords.difference R d (per:=per) file fk cut road Y (turn cell) (place cell) s)) fare):
    Billed φ (R.family.S.a f) scale (R.family.side f per)
      (fun cell=>R.family.omega N per (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s)-(ear R d (per:=per) file fk cut road Y (turn cell) (place cell) s)-(WilsonOriginalTwoFlatGridScaling.gap R N per u (road.trans cut) (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s))) fare:=by
  have same (cell:Fin k→Site (R.family.side f per)) := WilsonMeasuredPublicEntrancePinnedPass.phase R d (per:=per) file fk cut road Y (turn cell) (place cell) s
  refine Eq.mpr (congrArg (fun v=>Billed φ (R.family.S.a f) scale (R.family.side f per) v fare) (funext fun cell=>?_)) _sold
  linear_combination same cell

def radial (W:V u)(T:V K→ℂ):ℂ:=
  readingAt R (N:=N) (numerator R N per K T) road W

def shift (W:V u)(T:V N→ℂ):ℂ:=
  R.family.omega N per T-actualTransport R.family (N:=N) T (road.trans cut) W

theorem held (φ:Test k)(scale fare:ℝ)(W:(Fin k→Site (R.family.side f per))→V u)
    (_sold:Billed φ (R.family.S.a f) scale (R.family.side f per)
      (fun cell=>WilsonMeasuredPublicEntranceHeldCells.difference R d (per:=per) file fk cut road Y (turn cell) (place cell) s (W cell)) fare):
    Billed φ (R.family.S.a f) scale (R.family.side f per)
      (fun cell=>R.family.omega N per (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s)-radial R (N:=N) road (W cell) (submitted R d (N:=N) (per:=per) file fk Y (turn cell) (place cell) s)-
        shift R cut road (W cell) (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s)) fare:=by
  refine Eq.mpr (congrArg (fun v=>Billed φ (R.family.S.a f) scale (R.family.side f per) v fare) (funext fun cell=>?_)) _sold
  have cont:Continuous (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s):=continuous_finsetProd _ fun i _=>R.family.continuousO _ _ _ _ _
  have exactAt:readingAt R (N:=N) (credit R.family N per 0 (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s) K cut) road (W cell)=
      actualTransport R.family (N:=N) (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s) (road.trans cut) (W cell):=by
    unfold readingAt
    rw [WilsonThermometerUnitFilingCoarse.cutoff R cut road _ cont,←WilsonSeparatedOriginalSlabHeldProxy.normalized R (road.trans cut) (physical R d (f:=f) (N:=N) (per:=per) Y (turn cell) (place cell) s)]
    ring
  unfold radial shift WilsonMeasuredPublicEntranceHeldCells.difference
  rw [exactAt]
  ring

end YM.Integration.WilsonMeasuredPublicEntranceProfilePhase
end

