import YM.Integration.WilsonSeparatedPrefixChargedSeed
import YM.Integration.WilsonSeparatedPrefixPhysicalCredit
import YM.Integration.WilsonMeasuredPublicEntranceEntered

/-! Restore the charged complete entrance on the fixed independent optical file, with the actual N-source and all engineering factors at K. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixFiledUpper
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonMovingForkMixedSeed
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){f N per K u:ℕ}
local notation "C" => R.family

def originalWord (_top:f≤N)(site:Fin n → Cover)(Y:∀i,(C).label (d i))(c:Fin n→ℂ):
    Cut (C) N per:=fun U=>∏a∈(Stock.final (Fin n)).val,c a *
      (C).O N per (displayed R (d a) (Y a) (1,false)) (anchorAt R (snap (C) f per site a) N) U

def independentWord (file:Filed R d K)(fk:f≤K)(site:Fin n → Cover)(Y:∀i,(C).label (d i))(c:Fin n→ℂ):
    Config G ((C).side K per) → ℂ:=
  let w:=doses R d file.station (N:=N) (per:=per) (file.A N per) Y
  WilsonAddressedFiniteGuardTrial.printed R d (N:=N) (seats (R:=R) fk per site) w
    (WilsonReflectedPublicTrialRoster.factor R K d c) WilsonOriginalAlternativeFiniteSource.fired (Stock.final (Fin n))

theorem continuous (w:∀i,(C).label (d i))(ξ:Fin n→Site ((C).side K per)):
    Continuous (product R d (N:=N) ξ w):=by
  apply continuous_finsetProd
  intro i _
  exact continuous_const.add (((C).localSection (d i)).continuous_places _ _)

theorem original (file:Filed R d K)(live:K≤N)(fk:f≤K)(held:u≤K)(site:Fin n → Cover)
    (Y:∀i,(C).label (d i))(c:Fin n→ℂ)(valid:∀i,c i≠0){wage:ℝ}(read:ℂ)
    (entered:read=actualTransport (C) (N:=N) (originalWord R d (per:=per) (fk.trans live) site Y c)
      (held.trans live) 1-actualTransport (C) (N:=N) (independentWord R d (N:=N) (per:=per) file fk site Y c) held 1)
    (paid:‖read‖≤wage):
    let w:=doses R d file.station (N:=N) (per:=per) (file.A N per) Y
    let ξ:=seats (R:=R) fk per site
    let raw:=product R d (N:=N) ξ w
    let physical:=word R d f N per (fk.trans live) site Y
    ‖reading R (N:=N) (credit (C) N per 0 physical K live) u held-
      reading R (N:=N) (numerator R N per K raw) u held‖≤(∏i,‖c i‖)⁻¹*wage:=by
  intro w ξ raw physical
  have bill:=WilsonSeparatedPrefixPhysicalCredit.restored R live held
    (WilsonSeparatedPrefixScreenedWord.funded R (p:=per) d (fk.trans live) site Y)
    (continuous R d (N:=N) w ξ) (∏i,c i) (Finset.prod_ne_zero_iff.mpr (fun i _=>valid i))
    (WilsonSeparatedPrefixChargedSeed.physical R (p:=per) d (fk.trans live) site Y c)
    (WilsonSeparatedPrefixChargedSeed.printed R d live ξ w c) (entered ▸ paid)
  simpa only [norm_prod] using bill

end YM.Integration.WilsonSeparatedPrefixFiledUpper
end
