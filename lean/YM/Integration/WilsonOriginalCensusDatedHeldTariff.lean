import YM.Integration.WilsonOriginalCensusDatedWindingFare
import YM.Integration.WilsonOriginalFiniteCollarWinding

/-! Purchase the dated annual rates before any higher cutoff. In each fixed
occupied face, all binders use the same angular tariff. The physical period
limit can therefore be priced by the total incoming salary of that face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedHeldTariff
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

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram
variable {G:Gauge}{n:ℕ}{R:Run G}{N i e:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}[Fintype I]{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N i e k σ B)
  (κ:(v:Fin n) → Knob (H.tests v))(pt:Fin n → Chamber)(b:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n) → Choice R k v)
  (x:Affinity.Wallet (room (Fin n)))


open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonOriginalCensusDatedSheets (winding)
open WilsonNeutralTwoPrintPathDatedWage
local notation "block" z:max => (B z).mode.val
local notation "ports" z:max => toe (block z) (H.pin z) (H.root z) (H.frill z)
local notation "older" => fixed R k κ pt N b (i+1) cells seed
local notation "scope" z:max d:max => mass k (block z)+d



variable {D : Fin n → ℕ}

structure Rates (R:Run G)(k:Fin n→ℕ)(κ:∀v,Knob (D v))(pt:Fin n → Chamber)
    (i top e:ℕ) where
  width : Finset (Fin n) → Fin (e+1) → ℕ → ℝ
  fare : Finset (Fin n) → Fin (e+1) → ℕ → ℝ
  positive : ∀J q r,0<width J q r
  paid : ∀J (a:Fin (e+1)) r N,top≤N → ∀(q:(v:Fin n)→Choice R k v)(n₀:Side)
    (y:Fin n → Cover)(cells:Digits R.family.path.levels (Fin n)),
    MarkU y J (spent R k N i e n₀ (fixed R k κ pt N top (i+1) cells q) y (cells i) J a r)
      ((fixed R k κ pt N top i cells q y J).2 a r) (width J a r) (fare J a r)

theorem purchase (R:Run G)(k:Fin n→ℕ)(κ:∀v,Knob (D v))(pt:Fin n → Chamber)
    (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (ask:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices ask R.kit)(e:ℕ):
    ∀ᶠ i:ℕ in atTop,∀top,i<top → Nonempty (Rates R k κ pt i top e):=by
  filter_upwards [WilsonNeutralTwoPrintPathItinerary.original (h:=D) R k κ pt simple quiet ask bought e] with i rate
  intro top lt
  have individual (J:Finset (Fin n))(a:Fin (e+1))(r:ℕ):=rate top lt J a.val r (by omega)
  choose C σ _ positive issued using individual
  exact ⟨⟨σ,C,positive,issued⟩⟩

def salary (s:(Stock.census (Fin n)).Mode):ℝ:=
  ∑z,if s=(B z).mode then ‖∏v∈(B z).mode.val,(x v).val‖*‖touch (H.source z) (block z)‖ else 0

def periodTariff (G:Gauge)(cap:ℕ)(n₀:Side)(ν C:ℕ→ℝ):ℝ:=
  ∑r∈range (cap+1),tariff (Loc G 1) r (ν r) (C r)*catchW (ν r/512) n₀

theorem split (s:(Stock.census (Fin n)).Mode)(d:ℕ)(ν C:Finset (Fin n)→ℕ→ℝ):
    WilsonOriginalCensusDatedWindingFare.price H x s d 1 (fun z=>ν (block z)) (fun z=>C (block z))=
      salary H x s * periodTariff G (mass k s.val+d) side (ν s.val) (C s.val):=by
  unfold WilsonOriginalCensusDatedWindingFare.price salary
  rw [Finset.sum_mul]
  refine sum_congr rfl fun z _=>?_
  by_cases selected:s=(B z).mode
  · simp only [if_pos selected,one_pow,mul_one]
    rw [selected]
    unfold periodTariff
    rw [Finset.mul_sum]
  · simp [selected]

theorem physical (j:ℕ)(cap:ℕ)(ν C:ℕ→ℝ)(positive:∀r,0<ν r):
    Tendsto (fun per:ℕ=>periodTariff G cap (R.family.side j per) ν C) atTop (𝓝 0):=by
  unfold periodTariff
  have one (r:ℕ):Tendsto (fun per:ℕ=>tariff (Loc G 1) r (ν r) (C r) *
      catchW (ν r/512) (R.family.side j per)) atTop (𝓝 0):=by
    simpa only [mul_zero] using
      (WilsonMarkedIndependentMixedOrderedWinding.disappears (b:=j) R (ν r/512)
        (div_pos (positive r) (by norm_num))).const_mul (tariff (Loc G 1) r (ν r) (C r))
  simpa only [sum_const_zero] using tendsto_finsetSum (range (cap+1)) (fun r _=>one r)

end YM.Integration.WilsonOriginalCensusDatedHeldTariff
end
