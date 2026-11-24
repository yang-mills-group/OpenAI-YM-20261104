import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardWitness
import YM.Integration.WilsonPhysicalStationMixedWickPose
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPhaseData
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

def Recovered (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort):Prop:=
  (type_of% (L.baseR)) ∧
    (type_of% (L.baseB)) ∧
    (type_of% (L.baseC)) ∧
    (type_of% (L.baseS)) ∧
    (type_of% (run.phases.depends)) ∧
    (type_of% (run.phases.at_words)) ∧
    (type_of% (run.phases.at_boundary)) ∧
    (type_of% (run.leading.equivariant)) ∧
    (type_of% (run.leading)) ∧
    (type_of% (run.leading.unit)) ∧
    (type_of% (run.leading.lead)) ∧
  ∀i,(type_of% (L.letters i)) ∧
    (type_of% (L.spins i)) ∧
    (type_of% ((L.cards i).fromPhase)) ∧
    (type_of% ((L.cards i).corner)) ∧
    (type_of% ((L.cards i).reveals)) ∧
    (type_of% (L.cores i)) ∧
    (type_of% (L.links i)) ∧
    (type_of% ((run.phases.isTheory i).total)) ∧
    (type_of% ((run.phases.isTheory i).adj)) ∧
    (type_of% ((run.phases.isTheory i).meets)) ∧
    (type_of% ((run.phases.isTheory i).localPairs)) ∧
    (type_of% ((run.phases.isTheory i).faithful)) ∧
    (type_of% ((run.phases.isTheory i).covariance)) ∧
    (type_of% ((run.phases.isTheory i).spectral)) ∧
    (type_of% ((run.phases.isTheory i).forward)) ∧
    (type_of% ((run.phases.isTheory i).unique)) ∧
    (type_of% ((run.phases.continued_stress i).hermitian)) ∧
    (type_of% ((run.phases.continued_stress i).rule))

theorem original (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort):Recovered run:=by
  refine ⟨L.baseR,
    L.baseB,
    L.baseC,
    L.baseS,
    run.phases.depends,
    run.phases.at_words,
    run.phases.at_boundary,
    run.leading.equivariant,
    run.leading,
    run.leading.unit,
    run.leading.lead,?_⟩
  intro i
  exact ⟨L.letters i,
    L.spins i,
    (L.cards i).fromPhase,
    (L.cards i).corner,
    (L.cards i).reveals,
    L.cores i,
    L.links i,
    (run.phases.isTheory i).total,
    (run.phases.isTheory i).adj,
    (run.phases.isTheory i).meets,
    (run.phases.isTheory i).localPairs,
    (run.phases.isTheory i).faithful,
    (run.phases.isTheory i).covariance,
    (run.phases.isTheory i).spectral,
    (run.phases.isTheory i).forward,
    (run.phases.isTheory i).unique,
    (run.phases.continued_stress i).hermitian,
    (run.phases.continued_stress i).rule⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicPhaseData
end
