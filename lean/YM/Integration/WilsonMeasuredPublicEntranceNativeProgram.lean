import YM.Integration.WilsonMovingForkReporterBothArms
import YM.Integration.WilsonMeasuredPublicEntranceNativeCocycle

/-! Original two-home selection with one map assigned to each incoming physical radius. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeProgram
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonMovingForkReporterFilament WilsonMovingForkReporterBraided
open WilsonMeasuredPublicEntranceNativeFrame WilsonMovingForkReporterBothArms
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {l:Ultrafilter (ℕ×ℕ)}
  {H:(Bel C.book).Hierarchy} {z:Arch C} (F:Final C f S) (J₀:ℝ→tower S)
  {radius:ℝ}(horizon:Set.Ioc (0:ℝ) radius→ℕ)(survey:∀s,Vane C (horizon s))
  (outer inner:ℕ→Set.Ioc (0:ℝ) radius)

theorem original (lead:Leading F J₀) (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (higher:Tendsto (fun i=>horizon (outer i)) atTop atTop) (lower:Tendsto (fun i=>horizon (inner i)) atTop atTop)
    (vanish₁:Tendsto (fun i=>(survey (outer i)).wheel.r) atTop (𝓝 0))
    (vanish₂:Tendsto (fun i=>(survey (inner i)).wheel.r) atTop (𝓝 0))
    (apart:∀ᶠ i in atTop,(survey (inner i)).wheel.r < (survey (outer i)).wheel.r)
    (stages₁:Tendsto (fun i=>(survey (outer i)).k) atTop atTop) (stages₂:Tendsto (fun i=>(survey (inner i)).k) atTop atTop)
    (paid₁:∀i,(survey (outer i)).checked f H (horizon (outer i))) (paid₂:∀i,(survey (inner i)).checked f H (horizon (inner i))):
    ∃ c:Pair (fun i=>survey (outer i)) (fun i=>survey (inner i)),∃ J:Scaling S,Scribe f J c.report z F.sector l F.room.kernel H ∧
      (∀i,J.r (2*i)=(survey (outer (c.pick i))).wheel.r ∧ J.r (2*i+1)=(survey (inner (c.pick i))).wheel.r) ∧
      (∀d,∀ᶠ i:ℕ in atTop,
        atRadius l horizon survey J₀ (outer (c.pick i)) d=J.U (2*i) d ∧
        atRadius l horizon survey J₀ (inner (c.pick i)) d=J.U (2*i+1) d) ∧
      ∀d,∃ A B:ℝ,1≤A ∧ 0≤B ∧ ∀ᶠ i in atTop,
        Filed (f:=f) (l:=l) J₀ J c.report d (2*i) A B ∧ Filed (f:=f) (l:=l) J₀ J c.report d (2*i+1) A B := by
  obtain ⟨c,J,school,dates,dues⟩:=WilsonMovingForkReporterBothArms.original F J₀ lead made simple bliss
    higher lower vanish₁ vanish₂ apart stages₁ stages₂ paid₁ paid₂
  obtain ⟨Y,owned⟩:=school.meters
  exact ⟨c,J,school,dates,fun d=>WilsonMeasuredPublicEntranceNativeParity.original
    l horizon survey J₀ outer inner c owned d,dues⟩

end YM.Integration.WilsonMeasuredPublicEntranceNativeProgram
end
