import YM.Integration.WilsonOriginalHomogeneousBoxJets
import YM.Integration.WilsonOriginalCompactTorusChart

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousBoxContinuity
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)



theorem original {n m : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    (r : ℝ) (hr : 0 < r) (origin : Points n) (embed : (Fin m → ℝ) →L[ℝ] Points n)
    (a : Fin m → ℝ) (room : ∀ x : Fin m → ℝ, (∀ j, x j ∈ Icc (a j) (a j+1)) →
      origin+embed x ∈ conf n) :
    ContinuousOn (fun x => S.classMoment S d (r • (origin+embed x))
      (fun j => homogeneous F J Z r (d j) (v j))) {x | ∀ j, x j ∈ Icc (a j) (a j+1)} := by
  have linear : Continuous (fun x : Fin m → ℝ => embed x) := embed.continuous
  have affine : Continuous (fun x : Fin m → ℝ => origin+embed x) := continuous_const.add linear
  have lift : Continuous (fun x : Fin m → ℝ => r • (origin+embed x)) := affine.const_smul r
  have targets : MapsTo (fun x => r • (origin+embed x))
      {x | ∀ j, x j ∈ Icc (a j) (a j+1)} (conf n) :=
    fun x hx => Work.A05.smul_conf hr (room x hx)
  exact (S.class_smooth S F.room.kernel.smooth
    (fun j => ⟨d j,homogeneous F J Z r (d j) (v j)⟩)).continuousOn.comp lift.continuousOn targets

end YM.Integration.WilsonOriginalHomogeneousBoxContinuity
