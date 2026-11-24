import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCutoffJets
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodicStencils
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFixedStencils
open Filter Set Spec Table Extraction Next.UVStress
open PhysicalNext.Repeat.Legato
open PhysMS
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
    {order : Extraction.Order} {S : Table R.family.book}


open MeasureTheory FullVolume Function Lattice RG Wilson Extraction.Lease Difference Gaps Cells Asymptotics
open scoped ContDiff
theorem original {axis:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε s R T W):
    FullVolume.FixedBounds R.family ∧
    ∃row:(p n:ℕ)→(Fin n→R.family.book.Token)→Points n→ℂ,
      ∀p n:ℕ,∀v:Fin n→R.family.book.Token,
        ContDiffOn ℝ ∞ (row p n v) (NoHit R.family.S p n) ∧
        (∀t:Test n,suitable R.family.S p t→Tendsto (fun N=>Order.smears R.family N p v t) atTop (𝓝 (t.applyTo (row p n v)))) ∧
        ∀l:List (Reach n),
          let raw N:=squall (R.family.S.a N) l (lifted R.family N p v)
          let smooth:=derive (row p n v) (l.map Reach.where_)
          (∀{K:Set (Points n)},IsCompact K→K⊆NoHit R.family.S p n→∀δ:ℝ,0<δ→∀ᶠN:ℕ in atTop,
            ∀a:Positions n,tag (R.family.S.a N) a∈K→‖raw N a-smooth (tag (R.family.S.a N) a)‖≤δ) ∧
          Cluster R.family .full p n raw smooth ∧
          Meets (NoHit R.family.S p n) (fun N=>interpolated R.family.S N (raw N)) smooth ∧
          ∀t:Test n,suitable R.family.S p t→Integrable (fun x:Points n=>t x*smooth x) ∧
            Tendsto (fun N=>sumOn raw R.family.S p N t) atTop (𝓝 (t.applyTo smooth)):=by
  obtain ⟨whole,row,paid⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCutoffJets.original paid
  refine ⟨whole,row,?_⟩
  intro p n v
  obtain ⟨smooth,smears,each⟩:=paid p n v
  refine ⟨smooth,smears,?_⟩
  intro l
  obtain ⟨clusters,tiles,tests⟩:=each l
  exact ⟨fun compact inside δ pos=>WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodicStencils.original clusters compact inside pos,clusters,tiles,tests⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFixedStencils
end
