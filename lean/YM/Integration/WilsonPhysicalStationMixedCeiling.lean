import YM.Integration.WilsonPhysicalStationMixedBilledPort
import YM.Integration.WilsonPhysicalStationWickCeiling
/-! Fixed separated compact bound on every genuine free mixed-grade two-site vote. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedCeiling
open Function Set Filter Lattice Wilson RG Source Cells
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationMixedWickTest (fields reference)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedBilledPort (base)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(h:ℕ){r:ℕ}(z:(standard R.family).Field r)
theorem smooth (a:(R.family.labels.level h).Index):
    ContinuousOn (fun x:Points 2=>base R h z x a) (conf 2):=by
  let d:=grades h r
  let row:=fields R.family (l:=h) (Pi.single a 1) z
  let v:=fun j=>(standard R.family).representative (d j) (row j)
  change ContinuousOn (fun x=>(standard R.family).value d x v) (conf 2)
  exact ((Maxwell.table_smooth R.family.labels).on_conf d v).continuousOn

theorem original (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2):
    ∃ C:ℝ,0≤C ∧ ∀x∈K,∑a:(R.family.labels.level h).Index,‖base R h z x a‖≤C:=by
  classical
  have bounded (i:(R.family.labels.level h).Index):∃ u:ℝ,∀x∈K,‖base R h z x i‖≤u:=by
    obtain ⟨u,cap⟩:=compact.bddAbove_image ((smooth R h z i).norm.mono clear)
    exact ⟨u,fun x hx=>cap ⟨x,hx,rfl⟩⟩
  choose u cap using bounded
  refine ⟨∑a,|u a|,Finset.sum_nonneg (fun _ _=>abs_nonneg _),?_⟩
  exact fun x hx=>Finset.sum_le_sum (fun i _=>(cap i x hx).trans (le_abs_self _))
end YM.Integration.WilsonPhysicalStationMixedCeiling
end
