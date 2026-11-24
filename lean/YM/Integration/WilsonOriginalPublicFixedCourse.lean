import YM.Integration.WilsonOriginalPublicFixedCells
import YM.Integration.WilsonReceivedFixedDigitProgram
import YM.Integration.WilsonCapturedPrimaryWeakTrialFixedSites
import YM.Integration.WilsonOriginalPublicTrialMarkedHearing
import YM.Integration.WilsonThermometerOwnOffsetTale

/-! The original microscopic site supplies every digit on a fixed window.
At the bottom of this very itinerary the full old vacuum pays the finite and
folded marked coefficient, with the actual externally fitted source doses. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicFixedCourse
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

open WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Carp Source Multi Table Cells MeasureTheory
open WilsonSeparatedOriginalThermometerCells (positions placed weight variation tested)

open WilsonReceivedFixedDigitHistory (Digits itinerary)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVerseWeighted (full)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonThermometerDeclaredSeeds XSpace OriginalMarkedSourceComet
open WilsonCapturedPrimaryWeakTrialFixedInput (places)
open WilsonOriginalPublicTrialInput (fitted salary)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Carp
variable {G:Gauge}(R:Run G){N:ℕ}(per:ℕ)
local notation "Sites₃" => (Fin 3 → Site (R.family.side N per))

def sites (m:ℕ)(hm:m≤N)(x:Sites₃):Fin 3 → Site (R.family.side m per):=
  (R.family.S.toDepth hm per).parent ∘ x

def digits (x:Sites₃):Digits R.family.path.levels (Fin 3):=fun i v=>
  if hi:i+1≤N then (R.family.S.oneStep i per).residue (sites R per (i+1) hi x v) else 0

def home (m:ℕ)(hm:m≤N)(x:Sites₃)(c:Fin 3):Fin 3 → Cover:=
  PeriodicMarkedWinding.roots (R.family.side m per) (sites R per m hm x) c

theorem located (m:ℕ)(hm:m<N)(x:Sites₃)(c v:Fin 3):
  wrap (R.family.side (m+1) per) ((R.family.S.oneStep m per).count.val • (home R per m hm.le x c v)+
    lift (digits R per x m v))=sites R per (m+1) hm x v:=by
  have delta:digits R per x m v=(R.family.S.oneStep m per).residue (sites R per (m+1) hm x v):=by
    unfold digits
    rw [dif_pos (show m+1≤N by omega)]
  rw [delta]
  apply WilsonCapturedPrimaryWeakTrialFixedSites.wrapped (R.family.S.oneStep m per) rfl
  rw [show wrap _ (home R per m hm.le x c v)=sites R per m hm.le x v from
    congrFun (PeriodicMarkedWinding.roots_wrap (sites R per m hm.le x) c) v]
  exact Next.Rank.Station.parent_nested (R.family.S.oneStep m per) (R.family.S.toDepth hm per) (R.family.S.toDepth hm.le per)
    (R.family.S.block_odd m) (R.family.S.toDepth_odd hm per) (x v)

variable (d:Fin 3 → ℕ){h:Fin 3 → ℕ}(κ:(v:Fin 3) → Knob (h v))(pt:Fin 3 → Chamber)
def table (m b:ℕ)(hm:m≤N)(x:Sites₃)(c:Fin 3)(S:Finset (Fin 3))(q:Selection R d S):=
  itinerary R.family.path.levels R.metals.O d N (digits R per x) (b-m) m
    (start R d κ pt (full R d q)) (home R per m hm x c) S

theorem deposited (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m≤b → ∃σ B:ℝ,0<σ ∧ 1≤B ∧
    ∀N,b≤N → ∀(per:ℕ)(x:Fin 3→ Site (R.family.side N per))(c:Fin 3)(S:Finset (Fin 3))
      (q:Selection R d S)(hm:m≤N)(a:ℕ),a≤e → ∀rank,
      let F:=table R per d κ pt m b hm x c S q
      MarkU (home R per m hm x c) S (F.1 (R.family.side m per) a rank) (F.2 a rank) σ (B^S.card):=by
  obtain ⟨A,one,paid⟩:=WilsonReceivedCanonicalVerseRegister.original R d κ pt e zero_lt_one
  filter_upwards [WilsonReceivedFixedDigitProgram.original (h:=h) R simple quiet price funded d e] with m window
  intro b past
  obtain ⟨σ,C,hs,hC,bought⟩:=window b past 1 zero_lt_one
  refine ⟨σ,C*A,hs,one_le_mul_of_one_le_of_one_le hC one,?_⟩
  intro N high per x c S q hm a ha rank
  have born:=paid (full R d q)
  exact bought N high per (digits R per x) _ born.1 A one (born.2.2 _) (home R per m hm x c) S a ha rank

end YM.Integration.WilsonOriginalPublicFixedCourse
end
