import YM.Integration.WilsonReceivedChronologicalLedger
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldCorridor

/-! The actual upper inlet bought on the physical flat is exactly the signed public-basis entrance in the dated sum. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalHeldEntrance
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
open WilsonReceivedFirstTrace
open Pert.Asymptotics
open Filter WilsonThermometerMixedCollarSubpower
open WilsonThermometerMixedCollarSubpower
open Multi WilsonOriginalAlternativeTrialFunded
open QuadraticLocal.Tint QuadraticLocal.Advent.Oak QuadraticLocal.Earn Filter MeasureTheory
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonMeasuredPublicEntranceSignedEar (weighted)
open Labels Source RG12 Extra.Histories Motion Bandage Trace.Physical.GermGraph
open WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale
open WilsonThermometerMarchSource WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open RG05Readout RG05Readout.Native RG05Readout.Address Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout.Many RG05Readout.Pantry Records WilsonThermometerUnitFilingCoarse
open WilsonAddressedAlignedColumn WilsonReflectedPublicOrientedFaces
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
open Finset MeasureTheory Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonOriginalMicroscopicEntranceGridRow (factor pin)
open WilsonOriginalMicroscopicEntranceDoseBoard (Board source)
open WilsonOriginalMicroscopicEntranceTwoExits (originalRead)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonMeasuredPublicEntrancePanel (Panel Raw Guard charged)
open WilsonOriginalMicroscopicEntranceHeldMasterRead (ReadingAt)
open WilsonOriginalMicroscopicEntranceDoseBoard (Board source)
open WilsonOriginalMicroscopicEntrancePooledBoard (actual)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntranceGridRow (pin factor)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n requested power t:ℕ}{B:ℝ}
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G ((C).side i per)
variable (cut:f+n≤N)(A:Panel R d N per f (f+n) (Nat.le_add_right f n) cut requested power t B) (live:f<N)

def cohort:Board R d N per f A.loc t where
  live:=live
  sight:=A.sensors
  frames:=A.stamps
  home:=A.home
  entered:=A.enrolled
  x:=A.names
  motion:=A.turn
  filed:=A.filed
  salary:=fun a=>|charge (offer R (A.names a) (A.home a) live.le)|
  priced:=by
    intro a
    apply le_trans _ (le_max_right _ _)
    have h:=le_abs_self (charge (offer R (A.names a) (A.home a) live.le))
    linarith [abs_nonneg (charge (offer R (A.names a) (A.home a) live.le))]

def dose (a:Fin 3):ℂ:=charged R d A a

def coords (a:Fin 3):(C).label (d a):=Motion.patch ((C).labels.level (d a)) (A.turn a)
  ((A.axis a).symm (fitted R (d a) (A.slot a) N per (A.names a)))

local notation "c" => dose R d cut A
local notation "v" => coords R d cut A
local notation "B₀" => cohort R d cut A live
local notation "lit" => WilsonOriginalAlternativeFiniteSource.fired (V:=Fin 3)

theorem original {u:ℕ}(uf:u≤f)(W:X u)(heard:ReadingAt R d A uf W)(s:(J).Mode):
    let entered:=mass (c) s*WilsonOriginalMicroscopicEntranceTwoExits.originalRead R d (p:=per)
      (f:=f) (n:=n) cut (source R (B₀)) A.loc (v) s uf W
    entered=actualTransport (C) (N:=N) (Raw R d A s) ((uf.trans fk).trans cut) W-
      actualTransport (C) (N:=N) (Guard R d A s) (uf.trans fk) W ∧
      ‖entered‖≤((R.family.path.levels.clock.hatBeta f)^requested)⁻¹:=by
  intro entered
  obtain ⟨_top,_bottom,_rest,purchase⟩:=WilsonOriginalMicroscopicEntranceHeldCorridor.original R d cut A uf W heard
  have recast:=WilsonOriginalMicroscopicEntrancePooledBoard.joined R d (B₀) cut (v) s (c) uf W
  have eq:entered=actualTransport (C) (N:=N) (Raw R d A s) ((uf.trans fk).trans cut) W-
      actualTransport (C) (N:=N) (Guard R d A s) (uf.trans fk) W:=recast
  exact ⟨eq,by rw [eq,←(purchase s).2.1];exact (purchase s).2.2⟩

end YM.Integration.WilsonReceivedChronologicalHeldEntrance
end
