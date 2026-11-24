import YM.Integration.WilsonOriginalCoverNominalCubic

/-! Every deposited connected pair, including AB, enters the ordinary
three-mark input with the unchanged singleton at the remaining site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalPartition
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open WilsonSeparatedOriginalJointLog
open scoped Classical BigOperators
local notation "J" => WilsonSeparatedOriginalJointLog.three

theorem incoming {r : ℕ} (x : Grade J r) (unit : UnitLeading x) :
    let P := render (ratio x)
    let read := fun s:Finset (Fin 3) => slot (shape s) P
    let received := fun s:Finset (Fin 3) => slot (shape s) (logSeries (Fintype.card (Fin 3)+r) P)
    read univ =
      received univ + received {0,1} * read {2} + received {0,2} * read {1} +
        received {1,2} * read {0} + read {0} * read {1} * read {2} := by
  intro P read received
  have two (a b : Fin 3) (apart : a≠b) :
      received {a,b} = read {a,b} - read {a} * read {b} :=
    WilsonIndependentOrdinaryPairGrade.pair x unit a b (shape {a,b}) apart rfl
  have top : received univ = WilsonOriginalCoverNominalCubic.cubic read :=
    WilsonOriginalCoverNominalCubic.integrated x unit
  rw [top,two 0 1 (by decide),two 0 2 (by decide),two 1 2 (by decide)]
  unfold WilsonOriginalCoverNominalCubic.cubic
  ring

end YM.Integration.WilsonOriginalCoverNominalPartition
