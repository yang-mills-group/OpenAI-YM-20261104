import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalTrainGeometry
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalUnselectedWords
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalTrainMoments
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Function Set MeasureTheory
open scoped Topology NNReal BigOperators InnerProductSpace
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem value (i : F.α.space.X) (w : YM.Row.Core C.book) :
    F.α.space.character i (YM.OS.Ground.M F.α.unselected w.val w.property) =
      (F.α.ensemble i).expect w.val := by
  let qualified := YM.OS.Spread.Resolution.place_exists w.property
  exact (F.phase.phase.chosen i w.val w.property qualified.choose qualified.choose_spec.choose
    qualified.choose_spec.choose_spec).symm

theorem original {k : ℕ} (v : Fin k → YM.Row.Core C.book) :
    Tendsto (fun n => ObservablePhases.read (hierarchy F Q) none
      (YM.OS.Ground.all (OriginalTrainGeometry.cars v) n)) atTop
        (𝓝 (∫ χ, ∏ j, (F.α.ensemble χ).expect (v j).val ∂F.α.space.μ)) := by
  let q := OriginalTrainGeometry.cars v
  obtain ⟨separate,ascend⟩ := YM.OS.Ground.arcs F.α.unselected F.phase.phase.still
    F.room.kernel q (OriginalTrainGeometry.line v)
  have result := ascend.congr' (separate.mono fun n hn => (OriginalUnselectedWords.mean F Q _ hn).symm)
  rw [← F.phase.phase.decomposition.ground (YM.OS.Ground.starU F.α.unselected (q.map Prod.fst))] at result
  have eqn (χ : F.α.space.X) : F.α.space.character χ
      (YM.OS.Ground.starU F.α.unselected (q.map Prod.fst)) =
      ∏ j, (F.α.ensemble χ).expect (v j).val := by
    simp only [YM.OS.Ground.starU, q, OriginalTrainGeometry.cars, List.map_ofFn]
    rw [map_list_prod (F.α.space.character χ), List.map_ofFn, List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro j _
    exact value F χ (v j)
  simpa only [eqn] using result
end IssuedBridge.OriginalTrainMoments
end
