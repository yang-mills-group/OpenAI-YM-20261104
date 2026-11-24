import YM.Integration.WilsonOriginalObservedRoseBornChiralProper
import YM.Integration.WilsonPositionProgramTrialAccrued

/-! The genuine one-point values on an original filed leg, with its
unmarked history and its proper fitted and stable contributions. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralZeroTile
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

open WilsonOriginalObservedRoseBornChiralProper (submitted atGrade stableFee fittedFee)
open WilsonPositionProgramTrialAccrued (home)

theorem unissued (X:CutsP H T p v E W K U)(source:X.tileP=0):dose X 1=0:=by
  have silent:music (relativeF X.ax X.tx X.N X.m X.i) (0:Verse F)=0:=by
    funext i
    exact map_zero _
  rw [dose,one_smul,source,WilsonIndependentMatchedReportedProxy.reported,street,silent,Matrix.mulVec_zero]

theorem account {Q:SealR G}{rail:Rails Q.h k u e}
    (X:CutsP H Q.ans Q.path rail E W K U)(source:X.tileP=0):home Q X=0:=by
  have silent:music (relativeF X.ax X.tx X.N X.m (X.ceilC-X.m)) (0:Verse Q.F)=0:=by
    funext i
    exact map_zero _
  rw [WilsonPositionProgramTrialAccrued.tally,source,WilsonPositionProgramTrialFittedLens.ticket,
    street,silent,Matrix.mulVec_zero]
  funext i
  simp only [WilsonPositionProgramTrialFittedLens.matrix,Pi.zero_apply,smul_zero,Finset.sum_const_zero]

theorem cutoff (X:CutsP H T p v E W K U)(source:X.tileP=0)(φ:Rarity D)(B y:ℝ):
    fittedFee X φ B y=0:=by
  simp [fittedFee,unissued X source,cost,chargeBelow]

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U)(φ:Rarity D)(B y:ℝ)(o:CellR),X.tileP=0 →
    On h X.pt → Amplitude φ B → ∀q ≤ e,∀ω:Fin 0→YForest G,
    atGrade (receiving X 1 φ y o 0) q ω=0 ∧
    ‖atGrade (submitted X φ y o) q ω‖ ≤ stableFee X C φ B y:=by
  obtain ⟨C,pay⟩:=WilsonOriginalObservedRoseBornChiralProper.original H T p v E W K U
  refine ⟨C,?_⟩
  intro X φ B y o empty live good q hq ω
  have bought:=pay X φ B y o live good q hq ω
  obtain ⟨_,stable,fit⟩:=bought
  rw [cutoff X empty] at fit
  have zero:=norm_le_zero_iff.mp fit
  exact ⟨zero,by simpa only [zero,sub_zero] using stable⟩

end YM.Integration.WilsonOriginalObservedRoseBornChiralZeroTile
end
