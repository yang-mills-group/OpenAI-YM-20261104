import YM.Integration.WilsonNeutralTwoPrintPathPolynomial
import YM.Integration.WilsonNeutralTwoPrintPathCensus
import YM.Integration.WilsonNeutralTwoPrintPathBooked
import YM.Integration.WilsonNeutralTwoPrintPathRegistered
import YM.Integration.WilsonNeutralTwoPrintPathRankFare

/-! The signed lower-period polynomial uses the actual retained fixed child, full dated vacuum at the old cutoff and reprinted independent covered successor on the same mixed census. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathDatedPolynomial
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

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)
variable {G:Gauge}{n:ℕ}{k D:Fin n→ℕ}(R:Run G)(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)

open WilsonNeutralTwoPrintPathBooked (route)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathRankFare (tariff)


open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram
variable {n':Side}{I:Type}[Fintype I]{P:Passport n' (Fin n)}
  (B:I→Binder P (Stock.census (Fin n)))(x:Affinity.Wallet (room (Fin n)))
  (N b j e:ℕ)(cells:Digits R.family.path.levels (Fin n))(q:(v:Fin n)→Choice R k v)
  (c:I→Fin n)(o:I → Cover)(t:I → Case D)(u:∀i,Frill (B i).mode.val (c i))
local notation "J" i:max => (B i).mode.val
local notation "y" i:max => toe (J i) (c i) (o i) (u i)
local notation "old" => fixed R k κ pt N b (j+1) cells q
local notation "target" i:max => fixed R k κ pt N b j cells q (y i) (J i)
local notation "weight" i:max => ∏v∈(B i).mode.val,(x v).val
local notation "cut" i:max h:max => mass k (J i)+h
local notation "σshift" i:max => jog (wrap n' (o i))

def row (physical:Bool)(i:I)(h r:ℕ) :=
  if physical then spent R k N j e n' old (y i) (cells j) (J i) h r
  else plume ((target i).2 h r) n'
local notation "A" => row R κ pt B N b j e cells q c o u

def sheet (physical:Bool)(s:(Stock.census (Fin n)).Mode)(h:ℕ)(direction:Link G n'):ℂ:=
  ∑i,if s=(B i).mode then (weight i)*Complex.ofReal (diagonal (cut i h)
    (fun r z=>(touch (t i) (J i)) ((A) physical i h r ((σshift i) ∘ z)))
    (direction ∘ jog (B i).center)) else 0

def entry (s:(Stock.census (Fin n)).Mode)(h:ℕ)(p:Bool):MvPolynomial (Woods G n') ℝ:=
  ∑i,if s=(B i).mode then packed (fun r z=>phase p ((weight i)*Complex.ofReal
    ((touch (t i) (J i)) ((A) true i h r ((σshift i) ∘ (jog (B i).center).symm ∘ z)-
      (A) false i h r ((σshift i) ∘ (jog (B i).center).symm ∘ z))))) (cut i h) else 0

include B in
theorem filed (s:(Stock.census (Fin n)).Mode)(h:ℕ)(p:Bool)(direction:Link G n'):
    phase p (sheet R κ pt B x N b j e cells q c o t u true s h direction)-
        phase p (sheet R κ pt B x N b j e cells q c o t u false s h direction)=
      MvPolynomial.eval direction (entry R κ pt B x N b j e cells q c o t u s h p):=by
  unfold sheet entry
  rw [map_sum,map_sum,map_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  by_cases matchMode:s=(B i).mode
  · simp only [if_pos matchMode]
    exact WilsonNeutralTwoPrintPathPolynomial.compared (touch (t i) (J i)) (weight i) (σshift i)
      (jog (B i).center) ((A) true i h) ((A) false i h) (cut i h) p direction
  · simp [matchMode]

end YM.Integration.WilsonNeutralTwoPrintPathDatedPolynomial
end
