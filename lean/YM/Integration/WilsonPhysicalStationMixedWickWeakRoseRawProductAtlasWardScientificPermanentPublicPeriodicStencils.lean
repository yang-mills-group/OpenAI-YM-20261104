import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCutoffJets
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodicStencils
open Filter Set Spec Table Extraction Next.UVStress
open PhysicalNext.Repeat.Legato
open PhysMS
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}
    {order : Extraction.Order} {S : Table R.family.book}


open MeasureTheory FullVolume Function Lattice RG Wilson Extraction.Lease Difference Gaps Cells Asymptotics
open scoped ContDiff

theorem original {G:Gauge}{C:Family G}{e:Extraction.Sequence}{p n:ℕ}
    {F:ℕ→Positions n→ℂ}{v:Points n→ℂ}(actual:Cluster C e p n F v)
    {K:Set (Points n)}(compact:IsCompact K)(inside:K⊆NoHit C.S p n){ε:ℝ}(positive:0<ε):
    ∀ᶠ j:ℕ in atTop,∀a:Positions n,tag (C.S.a (e j)) a∈K→
      ‖F (e j) a-v (tag (C.S.a (e j)) a)‖≤ε:=by
  rw [Filter.eventually_atTop]
  by_contra! failed
  choose ix past addr within wrong using failed
  let tags:=fun k:ℕ=>tag (C.S.a (e (ix k))) (addr k)
  obtain ⟨point,owned,sub,strict,near⟩:=compact.isSeqCompact (show ∀k,tags k∈K from within)
  have cofinal:Tendsto ix atTop atTop:=tendsto_atTop_mono past tendsto_id
  have source:=actual.2 point (inside owned) (addr∘sub) (ix∘sub) (cofinal.comp strict.tendsto_atTop) near
  have target:=((actual.1.continuousAt ((nohitOpen C.S p n).mem_nhds (inside owned))).tendsto).comp near
  have gap:Tendsto (fun i=>‖F (e (ix (sub i))) (addr (sub i))-v (tags (sub i))‖) atTop (𝓝 0):=by
    simpa only [Function.comp_apply,sub_self,norm_zero] using (source.sub target).norm
  obtain ⟨i,success⟩:=(gap.eventually_lt_const positive).exists
  exact (not_lt_of_ge (wrong (sub i)).le) success

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodicStencils
end
