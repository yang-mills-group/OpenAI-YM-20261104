import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardCoordinates
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonMSDictionaryVector WilsonPositionHomogeneousFrame
open WilsonPositionSeparatedProfileMatching WilsonMacroscopicDetector
open scoped Topology BigOperators Classical


set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
variable {G:Gauge}{C:Family G}{S:Table C.book}

def splice (X:Scaling S)(J:ℝ→PhysMS.tower S)(s:ℝ):PhysMS.tower S:=
  if h:∃k,X.r k=s then X.U h.choose else J s

theorem selected (X:Scaling S)(J:ℝ→PhysMS.tower S)(k:ℕ):
    splice X J (X.r k)=X.U k:=by
  have hit:∃i,X.r i=X.r k:=⟨k,rfl⟩
  rw [splice,dif_pos hit,X.later.injective hit.choose_spec]

theorem away (X:Scaling S)(J:ℝ→PhysMS.tower S)(s:ℝ)(miss:¬∃k,X.r k=s):
    splice X J s=J s:=dif_neg miss

theorem original (X:Scaling S)(J:ℝ→PhysMS.tower S)(P:ℝ→PhysMS.tower S→Prop)
    (all:∀ᶠ s:ℝ in trail,P s (J s))(onX:∀ᶠ k:ℕ in atTop,P (X.r k) (X.U k)):
    (∀k:ℕ,splice X J (X.r k)=X.U k) ∧ ∀ᶠ s:ℝ in trail,P s (splice X J s):=by
  obtain ⟨k,hk⟩:=eventually_atTop.1 onX
  have before:∀ᶠ s:ℝ in trail,s<X.r k:=
    (eventually_lt_nhds (X.positive k)).filter_mono nhdsWithin_le_nhds
  refine ⟨selected X J,?_⟩
  filter_upwards [all,before] with s paid smaller
  by_cases hit:∃i,X.r i=s
  · obtain ⟨i,rfl⟩:=hit
    rw [selected]
    apply hk i
    by_contra bad
    exact lt_asymm smaller (X.later (lt_of_not_ge bad))
  · rw [away X J s hit]
    exact paid

theorem convergence {Y:Type*}[TopologicalSpace Y](X:Scaling S)(J:ℝ→PhysMS.tower S)
    (app:ℝ→PhysMS.tower S→Y)(y:Y)(all:Tendsto (fun s:ℝ=>app s (J s)) trail (𝓝 y))
    (onX:Tendsto (fun k:ℕ=>app (X.r k) (X.U k)) atTop (𝓝 y)):
    Tendsto (fun s:ℝ=>app s (splice X J s)) trail (𝓝 y):=by
  intro B near
  exact (original X J (fun s U=>app s U∈B) (all near) (onX near)).2

theorem sparse (X:Scaling S):Tendsto X.r atTop trail:=
  tendsto_nhdsWithin_iff.mpr ⟨X.drips,Eventually.of_forall X.positive⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame
end
