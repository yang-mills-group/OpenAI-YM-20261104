import YM.Integration.WilsonReportHarvestSlabLabels
/-! Shift the full original three-mark density before capture. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabShiftLabels
open Function Finset MeasureTheory Lattice RG Source Marker RG05Readout RG05Readout.Many
open Wilson Labels Address MergeProof Accent Menu Ribbons Ribbons.ManyCopies
open scoped Classical BigOperators
set_option quotPrecheck false
local notation "S" => Stock.census (Fin 3)
local notation "C₁" => Stock.census (Unit×Fin 3)
local notation "Z" => Stock.census (Unit×Unit)

open WilsonReportHarvestSlabLabels

def translated (v:Fin 3→ℂ)(F:Poly S):Poly S:=Poly.pass (Mach S v)*F

theorem lifted (v:Fin 3→ℂ) : filed (Mach S v)=Mach C₁ (v∘Prod.snd) := by
  unfold filed
  rw [feed_mach]
  congr 1
  funext j
  rw [Finset.sum_eq_single j.2]
  · rw [if_pos (show named j.2=j from Prod.ext (Subsingleton.elim _ _) rfl),one_mul];rfl
  · intro i _ hi
    rw [if_neg (fun h=>hi (congrArg Prod.snd h))]
  · simp

theorem read {G:Gauge} {n:Side}(F:Config G n→Poly S)(v:Fin 3→ℂ)(U:Config G n):
    (Pantry.pilot cohort policy (spice C₁ (v∘Prod.snd) (fun W=>filed (F W)) U)).part
      ((Z).fire ((),()))=(translated v (F U)).part entire := by
  have silent:(filed (Mach S v)).part (C₁).quiet=0:=by rw [lifted];exact mute _ _
  have carries:filed (translated v (F U))=spice C₁ (v∘Prod.snd) (fun W=>filed (F W)) U:=by
    unfold translated spice
    rw [map_mul,YM.Multi.pass_map _ _ (mute S v) silent,lifted]
  rw [←carries]
  exact WilsonReportHarvestSlabLabels.original _

end YM.Integration.WilsonReportHarvestSlabShiftLabels
