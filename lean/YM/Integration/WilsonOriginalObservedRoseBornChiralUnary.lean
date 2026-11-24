import YM.Integration.WilsonIndependentNotebookCubicCut
import YM.Integration.WilsonIndependentMatchedRosterLane
import YM.Integration.WilsonIndependentMatchedPhysicalArm
import YM.Integration.WilsonIndependentMatchedCoverGrade

/-! The genuine one-point values on an original filed leg, with its
unmarked history and its proper fitted and stable contributions. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralUnary
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Filter Function Matrix Lattice RG Laurent
open Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power Embroider Precision Exterior Fountain
open Soil Gauge Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedCoveredSeats WilsonIndependentMatchedFittedSeat
open WilsonIndependentMatchedReportedProxy (passport sectionSeal)
open scoped Topology BigOperators Classical
open WilsonIndependentMatchedRosterLane (chargeBelow)
open WilsonIndependentMatchedProxyIncome (tariff cost)
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}
variable {T:SectionData F}{p:h<D}{v:Rails h k u e}{E W K U:Credit}

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U)(φ:Rarity D)(B y:ℝ)(o:CellR),
    On h X.pt → Amplitude φ B →
    let δ:=paceT X.ax.S X.m X.ceilC
    let actual:=cruises X.ax X.tx X.N h X.ceilC X.m
      (WilsonIndependentNotebookCubicCut.raw X 1 φ y o)
    let rem:=seat X 1 φ y o 0
    let kept:=receiving X 1 φ y o 0
    actual=rem+kept ∧ Flush e 0 1 rem
      (chargeBelow φ 0 h 1 y ((C.buy X.Age*X.fuel)*δ^(1/4:ℝ)) B) ∧
    Flush e 0 1 kept (chargeBelow φ 0 h 1 y
      ((tariff H T p e 0 0 E W U).buy X.Age*cost e (dose X 1)) B):=by
  obtain ⟨C,pay⟩:=WilsonIndependentMatchedPhysicalArm.original H T p v E W K U
  refine ⟨C,?_⟩
  intro X φ B y o eligible test δ actual rem kept
  have base:Auth h (WilsonIndependentNotebookCubicCut.raw X 1 φ y o):=by
    simpa only [WilsonIndependentNotebookCubicCut.raw,one_smul,WilsonIndependentMatchedCoverProfile.word] using
      (locale_val _ (WilsonCoeffUV.Mer.placed h φ eligible _ _) _)
  have grades:=WilsonIndependentMatchedCoverGrade.carried X.ax X.tx X.vesselsC.hG X.vesselsC.green
    (Nat.le_add_right X.m X.i) (X.hc.trans X.hn) _ base v.hk
  obtain ⟨part,issued⟩:=WilsonIndependentNotebookCubicCut.dated X 1 φ y o 0 (Nat.zero_le _)
  have fixed:=pay X 1
  rw [abs_one,one_mul] at fixed
  have stable:=(WilsonIndependentMatchedRosterLane.stable X 1 φ y o δ _ B fixed test 0 0 (Nat.zero_le _)).billed 0 (Nat.zero_le _)
  have fit:=(WilsonIndependentMatchedRosterLane.filed X φ (dose X 1) y o δ B test 0 0).billed 0 (Nat.zero_le _)
  refine ⟨?_,?_,?_⟩
  · simpa only [Nat.add_zero,←grades] using (sub_eq_iff_eq_add.mp part).trans (congrArg (_+·) issued)
  · simpa only [Nat.add_zero,pace_self,div_one] using stable
  · simpa only [kept,WilsonIndependentMatchedFittedSeat.receiving,sectionSeal,Nat.add_zero,pace_self,div_one,Real.rpow_zero,mul_one] using fit

end YM.Integration.WilsonOriginalObservedRoseBornChiralUnary
end
