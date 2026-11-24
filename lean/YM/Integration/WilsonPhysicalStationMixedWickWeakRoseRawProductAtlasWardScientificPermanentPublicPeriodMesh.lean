import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicVolumeSelector

noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodMesh

open Function Filter Set MeasureTheory Spec Extraction Table
open scoped Topology Classical
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

variable {G:Gauge} {C:Family G}

/-- A fixed-period row uses all indices of the already chosen mesh. Each
later daughter of the same mesh has this same row at every suitable period. -/
def Fixed (C:Family G) (mesh:Extraction.Sequence) (n:ℕ) (tokens:Fin n→C.book.Token)
    (t:Test n) (row:ℕ→ℂ):Prop:=
  ∀period:ℕ, suitable C.S period t → Tendsto
    (fun N=>Order.smears C (mesh.choose N) period tokens t) atTop (𝓝 (row period))

def Arrives (C:Family G) (period:Extraction.Sequence) (n:ℕ) (tokens:Fin n→C.book.Token)
    (t:Test n) (row:ℕ→ℂ) (S:Table C.book):Prop:=
  (∀ᶠk:ℕ in atTop,suitable C.S (period.choose k) t) ∧
    Tendsto (fun k=>row (period.choose k)) atTop (𝓝 (t.applyTo fun x=>S.read x tokens))

theorem original {base:Extraction.Order}{raw:Table C.book}(before:base.Ordered C raw)
    (n:ℕ)(tokens:Fin n→C.book.Token)(t:Test n):
    ∃row:ℕ→ℂ, Fixed C base.mesh n tokens t row ∧
      ∀(request:Extraction.Sequence)(w:Extraction.Order)(S:Table C.book),
        let course:Extraction.Order:=(⟨base.mesh,request⟩:Extraction.Order).refine w
        course.Ordered C S → Arrives C (request.after w.per) n tokens t row S:=by
  classical
  obtain ⟨_,row,first,_⟩:=before.reads n tokens t
  refine ⟨row,first,?_⟩
  intro request w S course measured
  obtain ⟨suitablePeriods,other,meshLimit,volumeLimit⟩:=measured.reads n tokens t
  refine ⟨suitablePeriods,?_⟩
  have agree:∀period:ℕ, suitable C.S period t → other period=row period:=by
    intro period valid
    apply tendsto_nhds_unique (meshLimit period valid)
    exact (first period valid).comp w.mesh.monotone.tendsto_atTop
  exact volumeLimit.congr' (suitablePeriods.mono fun k hk=>agree _ hk)

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPeriodMesh
end
