import YM.Integration.WilsonOriginalMicroscopicEntranceDosePublic
import YM.Integration.WilsonOriginalNullOriginGridRoster
/-! An original, publicly enrolled cutoff product and its independently replanted K comparator at one real boundary. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDoseBoard
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ
open WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale WilsonThermometerReflectedTrajectory
open WilsonThermometerOwnOffsetNectar WilsonReflectedPublicOrientedFaces
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open WilsonAddressedAlignedColumn
open WilsonThermometerUnitFilingCoarse WilsonReflectedPublicOrientedFaces WilsonSeparatedPrefixCanonicalClearConvolution
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "I" => Fin 3
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)


open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceOpticalUnits (pole rank dye fare)
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open Trace.Physical.Germ Trace.Physical.GermGraph
open MeasureTheory WilsonOriginalMicroscopicEntranceTwoExits
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open OPE.Therm WilsonCoeffUV.Embroider
open WilsonOriginalMicroscopicEntranceGridRow (pin)

open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceHaloIncome (all)
open WilsonOriginalMicroscopicEntranceOpticalUnits (fare)
open WilsonOriginalMicroscopicGuardedFlat (count)
open WilsonOriginalMicroscopicEntrancePublicTrial (Restart)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)

/-- A measured roster at its three independently placed original sites. -/
structure Board (d:Fin 3→ℕ)(N per f:ℕ)(o:Fin 3→Site (R.family.side f per))(t:ℕ) where
  live : f<N
  sight : ∀i,Sight R.family (d i) per
  frames : ∀i,Emblems R.family (d i)
  home : ∀i,Opened R.family (d i) f per
  entered : ∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per (d i)
    (digits R N per 0) (sight i) (frames i)
  x : ∀i,R.family.label (d i)
  motion : Fin 3→Motion
  filed : WilsonThermometerReflectedRoster.filed R d (fun _=>0) motion o
    (fun i=>reduce (offer R (x i) (home i) live.le)) sight frames (Marks (Fin 3)) live.le t
  salary : Fin 3→ℝ
  priced : ∀i,charge (offer R (x i) (home i) live.le) ≤ max 1 (2*salary i)
variable {d:Fin 3→ℕ}{N per f t:ℕ}{o:Fin 3→Site (R.family.side f per)} (B:Board R d N per f o t)

def source (i:Fin 3):=displayed R (d i) (B.x i) (B.motion i)

def head (c:Fin 3→ℂ)(s:(Marks (Fin 3)).Mode)(U:Config G (R.family.side f per)):ℂ:=
  ∏i∈s.val,let y:=offer R (B.x i) (B.home i) B.live.le
           (c i*(charge y:ℂ))*(marked R (N:=N) 0 (B.motion i) (o i) (B.sight i) (B.frames i) (reduce y) f).2.1 U

def price (target:ℕ)(s:(Marks (Fin 3)).Mode):ℝ:=
  (∏i∈s.val,max 1 (2*B.salary i))*((R.family.path.levels.clock.hatBeta f)^target)⁻¹

def ancestry (per f:ℕ)(o:Fin 3→Site (R.family.side f per))(j:ℕ)(a:Unit×(Fin 3×Bool)):=
  WilsonOriginalNullOriginGridRoster.ancestry R per f (o a.2.1) j

theorem starts (per f:ℕ)(o:Fin 3→Site (R.family.side f per)):
    ancestry R per f o f=(o∘Prod.fst) ∘ Prod.snd:=
  funext fun a=>WilsonOriginalNullOriginGridRoster.starts R per f (o a.2.1)

theorem father (per f:ℕ)(o:Fin 3→Site (R.family.side f per)){j:ℕ}(hi:j<f):
    ancestry R per f o j=(R.family.path.levels.clock.op j per).ratio.parent ∘ ancestry R per f o (j+1):=
  funext fun a=>(WilsonOriginalNullOriginGridRoster.route R per f (o a.2.1) hi).symm

theorem original (d:Fin 3→ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (pace:WilsonWindowReportingPace.Slow R.kit)(cater:Cater R.family R.doors)
    (wage:WilsonReportLampForecast.Ready R.family.path.levels)
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(window target t:ℕ):
    ∀ᶠ u:ℕ in atTop,∀{N per f:ℕ}{o:Fin 3→Site (R.family.side f per)}(B:Board R d N per f o t)
      (uf:u≤f),R.family.S.a u/R.family.S.a f≤(R.family.path.levels.clock.hatBeta f)^window →
      (R.family.path.levels.params f).supportExponent=100 → 5≤(R.family.path.rep N per f).p.B →
      (∀a b:Fin 3,a≠b → (R.family.path.rep N per f).p.B^2+1≤ separation (o a) (o b)) →
      2≤(R.family.path.levels.budget u).supportExponent → ∀W:Config G (R.family.side u per),
      flags (R.family.path.rep N per u).p.threshold W=∅ → ∀s:(Marks (Fin 3)).Mode,
      ∀(dose:Fin 3→ℂ),(∀a,dose a≠0) →
      Restart R d simple (N:=N) uf (source R B) o s W
        (fun U=>(mass dose s)⁻¹*head R B dose s U) (price R B target s):=by
  filter_upwards [WilsonOriginalMicroscopicEntranceDosePublic.original R d simple shop pace cater wage nested
    window target t] with u buy
  intro N per f o B uf span fixed wide apart age W clear s dose pos
  exact @buy N per f uf B.live B.sight B.frames B.home B.entered B.x B.motion o (ancestry R per f o)
    B.filed span fixed wide apart (starts R per f o) (fun k _=>father R per f o) age W clear s B.salary B.priced dose pos
end YM.Integration.WilsonOriginalMicroscopicEntranceDoseBoard
end
