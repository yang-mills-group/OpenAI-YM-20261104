import YM.Integration.WilsonOriginalCensusDatedPurchased

/-! A single lower physical period bounds every higher UV cutoff and every
multiple board in the copy expansion. Dependence on the submitted word is
through its actual total incoming salary in the requested face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedPeriodOpening
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


open WilsonOriginalCensusDatedHeldTariff (salary periodTariff Rates)

theorem nonneg (s:(Stock.census (Fin n)).Mode):0 ≤ salary H x s:=by
  unfold WilsonOriginalCensusDatedHeldTariff.salary
  apply sum_nonneg
  intro z _
  split_ifs <;> positivity

def envelope (G:Gauge)(cap:ℕ)(n₀:Side)(ν C:ℕ→ℝ):ℝ:=
  ∑r∈range (cap+1),|tariff (Loc G 1) r (ν r) (C r)| * catchW (ν r/512) n₀

theorem period (R:Run G)(j per cap:ℕ)(n₀:Side)(ν C:ℕ→ℝ)(pos:∀r,0<ν r)
    (tiles:(R.family.side j per).val ∣ n₀.val):
    periodTariff G cap n₀ ν C ≤ envelope G cap (R.family.side j per) ν C:=by
  have size:(R.family.side j per).val ≤ n₀.val:=Nat.le_of_dvd n₀.pos tiles
  unfold periodTariff envelope
  refine sum_le_sum fun r _=>?_
  have decay:catchW (ν r/512) n₀.val ≤ catchW (ν r/512) (R.family.side j per).val:=by
    unfold catchW
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left (by exact_mod_cast size) (neg_nonpos.mpr (div_nonneg (pos r).le (by norm_num)))
  refine (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le).trans ?_
  exact mul_le_mul_of_nonneg_left decay (abs_nonneg _)

theorem shrinks (R:Run G)(j cap:ℕ)(ν C:ℕ→ℝ)(pos:∀r,0<ν r):
    Tendsto (fun per:ℕ=>envelope G cap (R.family.side j per) ν C) atTop (𝓝 0):=by
  unfold envelope
  have one (r:ℕ):Tendsto (fun per:ℕ=>|tariff (Loc G 1) r (ν r) (C r)| * 
      catchW (ν r/512) (R.family.side j per)) atTop (𝓝 0):=by
    simpa only [mul_zero] using
      (WilsonMarkedIndependentMixedOrderedWinding.disappears (b:=j) R (ν r/512)
        (div_pos (pos r) (by norm_num))).const_mul |tariff (Loc G 1) r (ν r) (C r)|
  simpa only [sum_const_zero] using tendsto_finsetSum (range (cap+1)) (fun r _=>one r)

def Opened (R:Run G)(j per cap:ℕ)(ν C:ℕ→ℝ)(gross ε:ℝ):Prop:=
  ∀n₀:Side,(R.family.side j per).val ∣ n₀.val → ∀b:ℝ,0≤b → b≤gross →
  2*(b*periodTariff G cap n₀ ν C) ≤ ε

theorem original (R:Run G)(k₀:Fin n → ℕ)(κ₀:∀v,Knob (D v))(pt₀:Fin n → Chamber)
    {j top q:ℕ}(rates:Rates R k₀ κ₀ pt₀ j top q)(J:Finset (Fin n))(a:Fin (q+1))
    (gross:ℝ){ε:ℝ}(small:0<ε):∀ᶠ per:ℕ in atTop,
    Opened R j per (mass k₀ J+a.val) (rates.width J a) (rates.fare J a) gross ε:=by
  let cap:=mass k₀ J+a.val
  let ν:=rates.width J a
  let C:=rates.fare J a
  have gone:Tendsto (fun per:ℕ=>(2*gross)*envelope G cap (R.family.side j per) ν C) atTop (𝓝 0):=by
    simpa only [mul_zero] using (shrinks R j cap ν C (rates.positive J a)).const_mul (2*gross)
  filter_upwards [(tendsto_order.1 gone).2 ε small] with per ready
  intro n₀ divides b positive bounded
  have paid:=period R j per cap n₀ ν C (rates.positive J a) divides
  have envelopeNonnegative:0≤envelope G cap (R.family.side j per) ν C:=
    sum_nonneg fun r _=>mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ 2*(b*envelope G cap (R.family.side j per) ν C):=by gcongr
    _ ≤ (2*gross)*envelope G cap (R.family.side j per) ν C:=by
      rw [←mul_assoc]
      gcongr
    _ ≤ ε:=ready.le

end YM.Integration.WilsonOriginalCensusDatedPeriodOpening
end
