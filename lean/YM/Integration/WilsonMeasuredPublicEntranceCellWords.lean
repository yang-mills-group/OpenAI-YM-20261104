import YM.Integration.WilsonSeparatedPrefixPanelReturn
import YM.Integration.WilsonSeparatedPrefixCellProfile
/-! The true returned N-word and the independently measured K-word are heard at the same original ear before a signed smooth position sum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCellWords
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel Reading charged)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "J" => Stock.census (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}

open Extraction WilsonAddressedPhysicalCells

def physical (Y:∀v,(C).label (d v))(turn:Fin n→Motion)(o:Fin n→Site ((C).side f per))
    (s:(J).Mode):Config G ((C).side N per)→ℂ:=fun U=>∏v∈s.val,
  (C).O N per (displayed R (d v) (Y v) (turn v)) (anchorAt R (o v) N) U

def submitted (file:Filed R d K)(fk:f≤K)(Y:∀v,(C).label (d v))
    (turn:Fin n→Motion)(o:Fin n→Site ((C).side f per))(s:(J).Mode):Config G ((C).side K per)→ℂ:=
  let w:=fun v=>Motion.patch ((C).labels.level (d v)) (turn v)
    (doses R d file.station (N:=N) (per:=per) (file.A N per) Y v)
  fun U=>∏v∈s.val,uncut R (d v) N per K (((C).S.toDepth fk per).embed (o v)) (units R d K w v) U

def difference (file:Filed R d K)(fk:f≤K)(cut:K≤N)(road:u≤K)(Y:∀v,(C).label (d v))
    (turn:Fin n→Motion)(o:Fin n→Site ((C).side f per))(s:(J).Mode):ℂ:=
  reading R (N:=N) (credit (C) N per 0 (physical R d Y turn o s) K cut) u road-
    reading R (N:=N) (numerator R N per K (submitted R d (N:=N) file fk Y turn o s)) u road

theorem paid (A:Panel R d N per f K fk cut requested power t B)(file:Filed R d K)
    (station:A.slot=file.station)(axes:A.axis=file.A N per)(held:u≤f)(sale:Reading R d A held)
    (one:∀v,1≤A.M v)(E:Fin n→ℕ)(refs:∀v b,b≤d v→(C).ref b≤N)
    (fare:∀v,Next.Rank.Spindle.paid (C) (d v) f N per (A.names v)≤A.M v*(H f)^(E v))
    (s:(J).Mode)(desired:ℕ)(exposure:desired+∑v∈s.val,E v≤requested):
    ‖difference R d file fk cut (held.trans fk) A.names A.turn A.loc s‖≤
      (∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d v) (A.M v))*((H f)^desired)⁻¹:=
  WilsonSeparatedPrefixPanelReturn.measured R d A file station axes held sale one E refs fare s desired exposure

theorem profile {k:ℕ}(φ:Test k)(scale:ℝ)(file:Filed R d K)(fk:f≤K)(cut:K≤N)(road:u≤K)
    (Y:∀v,(C).label (d v))(turn:Sites ((C).side f per) k→Fin n→Motion)
    (place:Sites ((C).side f per) k→Fin n→Site ((C).side f per))(s:(J).Mode)(fare:ℝ)(nonneg:0≤fare)
    (sold:∀e,mass φ ((C).S.a f) scale ((C).side f per) e≠0 →
      ‖difference R d file fk cut road Y (turn e) (place e) s‖≤fare):
    let delta:=fun e=>difference R d file fk cut road Y (turn e) (place e) s
    let node:=atSite ((C).S.a f) scale ((C).side f per)
    φ.applyTo (fun x=>delta (node x))=∑e,mass φ ((C).S.a f) scale ((C).side f per) e*delta e ∧
      ‖φ.applyTo (fun x=>delta (node x))‖≤(∫x,‖φ x‖)*fare:=by
  intro delta node
  exact ⟨WilsonSeparatedPrefixCellProfile.tested φ _ _ _ ((C).S.a_pos f) delta,
    WilsonSeparatedPrefixCellProfile.priced φ _ _ _ ((C).S.a_pos f) delta fare nonneg sold⟩

end YM.Integration.WilsonMeasuredPublicEntranceCellWords
end
