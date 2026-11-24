import YM.Integration.WilsonIndependentMatchedReportedContrast
import YM.Integration.WilsonIndependentMatchedPivotSeat

/-! A true rooted seat also owns its coarse angular norm on each intermediate
date. This is the second input in the finite-arity first-connection theorem.
Both invoices use the same received tower before the next tested product. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterLane
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedCutBudget WilsonIndependentMatchedFittedSeat

open WilsonIndependentMatchedMixBudget WilsonIndependentMatchedCoverReception

open WilsonIndependentMatchedProxyIncome (tariff cost)
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open WilsonIndependentMatchedCoverPairBudget (Bought)
open WilsonIndependentMatchedPivotSeat (axis ticket)

def chargeBelow {D:ℕ}(φ:Rarity D)(u d:ℕ)(x y A B:ℝ):ℝ:=
  BasePrice d φ x y*((1+4*radiusH φ x y)^u*(B*A))

structure Lane {D:ℕ}(R:Realm G (e+1) E)(l d m n N u b:ℕ)(φ:Rarity D)(y:ℝ)(o:CellR)
    (δ α A B:ℝ)(P:ℕ→Era G ℝ):Prop where
  accounts : Funds R l d m n u b φ y o δ α A B P
  billed : ∀i ≤ n,let x:=paceT R.draws.S m (m+i)
    Flush e u x (P i) (chargeBelow φ u d x y (A*(δ/x)^α) B)
  pushed : ∀i<n,verseI R.draws R.paid (m+i) N l (P (i+1))=P i

theorem stable (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)
    (δ A B:ℝ)(paid:Bought X a δ A)(test:Amplitude φ B)(u b:ℕ)(room:u+b ≤ u₀):
    Lane X.vesselsC k h X.m X.i X.N u b φ y o δ (1/4) A B (seat X a φ y o):=by
  refine ⟨WilsonIndependentMatchedSeatedIncome.stable X a φ y o δ A B test u b room paid,?_,
    (traced X a φ y o).2⟩
  intro i hi x
  exact (census_br _ _ φ x y ((X.onward hi).μ a) ((X.onward hi).μ a) o u (pace_pos ..)
    (pace_le _ (Nat.le_add_right _ _)) test
    (fun j hj r=>YieldP.same (paid i hi j hj r u ((Nat.le_add_right _ _).trans room)) le_rfl) le_rfl h).f_l

theorem filed (X:CutsP H T p v E W K U)(φ:Rarity D)(d:Verse F)(y:ℝ)(o:CellR)
    (δ B:ℝ)(test:Amplitude φ B)(u b:ℕ):
    Lane X.vesselsC h h X.m X.i X.N u b φ y o δ 0 ((tariff H T p e u b E W U).buy X.Age*cost e d) B
      (printed X.vesselsC (sectionSeal T p) φ d X.m X.N y o):=by
  let C₁:=WilsonIndependentMatchedProxyIncome.credit H T p e (u+b) E W U
  let C₂:=WilsonIndependentMatchedProxyIncome.credit H T p e u E W U
  have high:1≤C₁.buy X.Age:=C₁.purchase X.windowC.warm
  have low:0≤C₂.buy X.Age:=zero_le_one.trans (C₂.purchase X.windowC.warm)
  have permit:C₂.buy X.Age*cost e d ≤ (tariff H T p e u b E W U).buy X.Age*cost e d:=by
    rw [tariff,Credit.products]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left low high) (WilsonIndependentMatchedProxyIncome.nn d)
  refine ⟨WilsonIndependentMatchedProxyIncome.original X φ d y o δ B test u b,?_,
    (wired X.vesselsC _ (passport X) φ d X.m X.N X.i X.ha (X.hc.trans X.hn) y o).2⟩
  intro i hi x
  have before:X.m+i ≤ X.N:=(Nat.add_le_add_left hi _).trans (X.hc.trans X.hn)
  have valid:=tournure (m:=X.m) X.L.L d (X.ha.trans (Nat.le_add_right X.m i)) before
  simp only [Real.rpow_zero,mul_one,printed,SealR.spins,FirstCharge,sectionSeal]
  exact (census_br _ _ φ x y valid valid o u (pace_pos ..) (pace_le _ (Nat.le_add_right _ _)) test
    (fun j hj r=>YieldP.same ((WilsonIndependentMatchedProxyIncome.row X d i hi j hj r u).more permit)
      le_rfl) le_rfl h).f_l

end YM.Integration.WilsonIndependentMatchedRosterLane
