import YM.Integration.WilsonOriginalConnectedSubmission
import YM.Integration.WilsonOriginalCensusDatedMaterial

/-! One common array of original locations, with one authentic original cable
and one rooted declared word for each of its nonempty physical subsets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFaceSites
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathJet (diagonal)

open WilsonOriginalConnectedSubmission (address)
open WilsonOriginalCensusDatedMaterial (Material)
open WilsonCoeffUV.Wheel.Address (toe)
variable {G:Gauge}{n:ℕ}(side:Side)(y:Fin n → Cover)
local notation "J" => Stock.census (Fin n)
local notation "I" => Hot (J)

def port:Passport side (Fin n):=Passport.point (fun v=>wrap side (y v))
def binder (s:I):Earn.Binder (port side y) (J):=address (port side y) s

def pin (s:I):Fin n:=s.property.choose
def root (s:I):Cover:=y (pin s)
def frill (s:I):Frill s.val.val (pin s):=fun v=>y v.val

theorem center (s:I):(binder side y s).center=wrap side (root y s):=rfl

theorem tariff (s:I):(binder side y s).length≤
    ∑v∈s.val.val,4*separation (wrap side (root y s)) (wrap side (y v)):=by
  rw [binder,WilsonOriginalConnectedSubmission.length]
  apply sum_le_sum
  intro v _
  exact Cable.link_height (wrap side (root y s)) (wrap side (y v))

theorem source (s:I)(v:Fin n)(hv:v∈s.val.val):
    toe s.val.val (pin s) (root y s) (frill y s) v=y v:=by
  by_cases anchored:v=pin s
  · subst v
    simp [toe,root]
  · have live:v∈s.val.val.erase (pin s):=mem_erase.mpr ⟨anchored,hv⟩
    simp [toe,anchored,live,frill]

theorem inherited {tests k:Fin n→ℕ}(Y:Outerm G tests)(well:Wellness k Y)(s:I)
    (t:Finset (Fin n))(ht:t⊆s.val.val):
    Y (toe s.val.val (pin s) (root y s) (frill y s)) t=Y y t:=
  well.filial _ _ _ (fun v hv=>source y s v (ht hv))

variable (R:Run G)(N i q:ℕ)(k tests:Fin n→ℕ)(σ amplitude allowance:ℝ)
  (realm:Realm G (q+1) Credit.leanC)(start:realm.anchor ≤ i)
  (paid:Paid R realm start tests k allowance σ)
  (prior:Input realm start (univ:Finset (Fin n)) k tests amplitude)
  (funded:0 ≤ amplitude)(live:i < N)(hs:0 < σ)
  (positive:∀v,0 < k v)(test:Case tests)
  (closed:Cloze tests k realm Credit.leanC)(tickets:Insure n (mass k univ) realm Credit.leanC)

def journal:Material R N i q k σ (binder side y) where
  tests:=tests
  available:=univ
  amplitude:=amplitude
  allowance:=allowance
  realm:=realm
  start:=start
  paid:=paid
  prior:=prior
  nonneg:=funded
  lower:=live
  radius:=hs
  pin:=pin
  included:=fun _=>subset_univ _
  marked:=fun s=>s.property.choose_spec
  positive:=fun s=>lt_of_lt_of_le (positive (pin s)) (Finset.single_le_sum (s:=s.val.val)
    (f:=k) (fun _ _=>Nat.zero_le _) s.property.choose_spec)
  root:=root y
  source:=fun _=>test
  frill:=frill y
  closed:=closed
  tickets:=tickets

end YM.Integration.WilsonOriginalCensusFaceSites
end
