import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardWitness
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardCoordinates
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Log Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score
open MS MS.Land MS.Fleet WilsonMSDictionaryVector WilsonPositionHomogeneousFrame
open WilsonPositionSeparatedProfileMatching WilsonMacroscopicDetector
open scoped Topology BigOperators Classical

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {L : EveryPhase.Almanac F}
    {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin} {J : ℝ → PhysMS.tower S}
    {Y : (Bel R.family.book).Hierarchy} {A : Trace.Terrace.Arch R.family}
    {ℓ : Ultrafilter (ℕ × ℕ)} {cohort : Ultrafilter (ℕ × ℕ) → Prop}
    {simple : G.Simple}

set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096


abbrev Port (R:Run G):=(Spin.comparator R.family.book).Field 4

def total (P:ℕ→Axis→Axis→Port R)(out:Port R→ₗ[ℂ]ℂ)(clock:ℝ→ℝ)(N:ℕ)(a b:Axis)(s:ℝ):ℂ:=
  ∑j:Fin (N+1),(clock s:ℂ)^j.val*out (P j.val a b)

def body (R:Run G)(κ d e:ℝ→ℝ)(s:ℝ)(a b:Axis):Port R:=
  κ s • standard4 R.family a b + d s • Trace.Pith.erase (stepField R.family) a b +
    e s • Trace.Pith.erase ((Bel R.family.book).unit 4) a b

theorem original (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort)
    (prior:ℝ→PhysMS.tower S)(price:WilsonPhysicalStationMixedWickPose.Receipt (Y:=ℓ) (Z:=A) simple F Y prior J):
    ∃(P':ℝ→Spin.change S 4)(χ:E4→ℝ)(κ d e:ℝ→ℝ),
      Trace.Target.XScheme F simple Y ℓ (fun s=>prior s 4) P' χ ∧
      Trace.Target.FieldComparison F Y A (fun s=>prior s 4) P' κ d e ∧
      Filter.Tendsto κ trail (𝓝 1) ∧
      (∀(P:ℕ→Axis→Axis→Port R)(out:Port R→ₗ[ℂ]ℂ)(a b:Axis)(N:ℕ)(clock:ℝ→ℝ),
        Filter.Tendsto (fun s:ℝ=>(out ((J s 4).symm (s^4 • F.sector.energy a b))-total P out clock N a b s)/(clock s:ℂ)^N) trail (𝓝 0) ↔
        Filter.Tendsto (fun s:ℝ=>(out (body R κ d e s a b)-total P out clock N a b s)/(clock s:ℂ)^N) trail (𝓝 0)) ∧
      (∀x∈conf 2,Filter.Tendsto (fun s=>S.classMoment (TraceExtension.selected F) (fun _=>4) (s • x)
          (fun _=>J s 4 (stepField R.family))) trail
        (𝓝 ((Bel R.family.book).classMoment (Bel R.family.book) (fun _=>4) x (fun _=>stepField R.family)))):=by
  obtain ⟨_,_,_,_,_,_,P',χ,κ,d,e,same,scheme,comparison,financial⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardWitness.original run prior price
  refine ⟨P',χ,κ,d,e,scheme,comparison,comparison.spinTwo,?_,?_⟩
  · intro P out a b N clock
    constructor <;> intro cost <;> apply cost.congr' <;>
      filter_upwards [financial] with s measured <;> simp only [measured.1 a b,body]
  · intro x gap
    apply (comparison.selectedScalar x gap).congr'
    filter_upwards [same] with s eq
    rw [eq]

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardCoordinates
end
