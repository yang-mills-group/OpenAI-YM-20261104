import YM.Integration.WilsonPhysicalStationMixedWickPose
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardWitness
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

def Verified (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (prior:ℝ→ PhysMS.tower S):Prop:=
  (∀i,(type_of% (run.phases.isTheory i)) ∧ (type_of% (run.phases.into_onto i)) ∧
      (type_of% (run.phases.euclid i)) ∧ (type_of% (run.phases.mink i)) ∧
      (type_of% ((run.phases.continued_stress i).appointment)) ∧
      (type_of% ((run.phases.continued_stress i).orbital)) ∧
      (type_of% ((run.phases.continued_stress i).symmetric)) ∧
      (type_of% ((run.phases.continued_stress i).hermitian)) ∧
      (type_of% ((run.phases.continued_stress i).conserve)) ∧
      (type_of% ((run.phases.continued_stress i).commutator)) ∧
      (type_of% ((run.phases.continued_stress i).rule))) ∧
    (type_of% run.phases.at_words) ∧ (type_of% run.phases.at_boundary) ∧
    (type_of% run.trace.identity) ∧ (type_of% run.trace.nonzero) ∧
    (∀P:ℕ→ ℕ→ Prop,
      ((∀ᶠz in f.fuse,P z.1 z.2) ↔ (∀ᶠperiod:ℕ in atTop,∀ᶠmesh:ℕ in atTop,
          P (f.mesh.choose mesh) (f.per.choose period))) ∧
      ((∀ᶠperiod:ℕ in atTop,∀ᶠmesh:ℕ in atTop,P (f.mesh.choose mesh) (f.per.choose period)) → 
          ∀ᶠz in (ℓ:Filter (ℕ×ℕ)),P z.1 z.2)) ∧
    ∃(P':ℝ→ Spin.change S 4)(χ:E4→ ℝ)(κ d e:ℝ→ ℝ),
      (∀ᶠs in trail,J s 4=P' s) ∧
      Trace.Target.XScheme F simple Y ℓ (fun s=>prior s 4) P' χ ∧
      Trace.Target.FieldComparison F Y A (fun s=>prior s 4) P' κ d e ∧
      ∀ᶠs in trail,(∀a b,(J s 4).symm (s^4 • F.sector.energy a b) =
        κ s • standard4 R.family a b + d s • Trace.Pith.erase (stepField R.family) a b +
          e s • Trace.Pith.erase ((Bel R.family.book).unit 4) a b) ∧
        s^4 • TraceExtension.center F =
          (4*d s) • TraceExtension.centerIn S (TraceExtension.selected F) ((J s 4) (stepField R.family))

theorem original (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort)
    (prior:ℝ→ PhysMS.tower S)(price:WilsonPhysicalStationMixedWickPose.Receipt (Y:=ℓ) (Z:=A) simple F Y prior J):
    Verified run prior:=by
  obtain ⟨P',χ,κ,d,e,same,scheme,comparison⟩:=price
  refine ⟨?_,run.phases.at_words,run.phases.at_boundary,run.trace.identity,run.trace.nonzero,?_,
    P',χ,κ,d,e,same,scheme,comparison,?_⟩
  · intro i
    have force:=run.phases.continued_stress i
    exact ⟨run.phases.isTheory i,run.phases.into_onto i,run.phases.euclid i,run.phases.mink i,
      force.appointment,force.orbital,force.symmetric,force.hermitian,force.conserve,force.commutator,force.rule⟩
  · intro predicate
    refine ⟨Iff.rfl,?_⟩
    intro ordered
    exact Filter.Eventually.filter_mono run.original (show ∀ᶠz in f.fuse,predicate z.1 z.2 from ordered)
  · filter_upwards [same,comparison.measures,comparison.centerComparison] with s common measured center
    rw [common]
    exact ⟨measured.reads,center⟩

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicWardWitness
end
