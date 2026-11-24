import YM.Integration.WilsonMovingForkReporterBothArms
import YM.Integration.WilsonMovingForkReporterSuppliedBatch

/-! The same two public columns have their full original heating stamps and a common increasing order and aperture. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterSignedBothArms
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonMovingForkReporterFilament WilsonMovingForkReporterBraided
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book} {l:Ultrafilter (ℕ×ℕ)}
  {H:(Bel C.book).Hierarchy} {z:Arch C} (F:Final C f S) (J₀:ℝ→tower S)
  {D E:ℕ→ℕ} {V:∀i,Vane C (D i)} {W:∀i,Vane C (E i)}

open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent

variable (B:Binding C) (O:HaarBudget G) (χ:ChartRatio G)
  (X:∀i,Tapes.Panel (D i)) (Y:∀i,Tapes.Panel (E i)) (n₁ n₂:ℕ→ℕ) (z₁ z₂:ℕ→ℝ)

theorem original (lead:Leading F J₀) (made:C.Makes) (simple:G.Simple) (bliss:Bliss F l z H)
    (higher:Tendsto D atTop atTop) (lower:Tendsto E atTop atTop)
    (vanish₁:Tendsto (fun i=>(V i).wheel.r) atTop (𝓝 0))
    (vanish₂:Tendsto (fun i=>(W i).wheel.r) atTop (𝓝 0))
    (apart:∀ᶠ i in atTop,(W i).wheel.r < (V i).wheel.r)
    (stages₁:Tendsto (fun i=>(V i).k) atTop atTop) (stages₂:Tendsto (fun i=>(W i).k) atTop atTop)
    (sat₁:∀i,(V i).checked f H (D i) ∧ WilsonMovingForkReporterNamedInk.Filed B made O χ (X i) (V i) (n₁ i) (z₁ i))
    (sat₂:∀i,(W i).checked f H (E i) ∧ WilsonMovingForkReporterNamedInk.Filed B made O χ (Y i) (W i) (n₂ i) (z₂ i)):
    ∃ c:Pair V W,∃ J:Scaling S,Scribe f J c.report z F.sector l F.room.kernel H ∧
      (∀i,J.r (2*i)=(V (c.pick i)).wheel.r ∧ J.r (2*i+1)=(W (c.pick i)).wheel.r) ∧
      (∀d,∃ A B':ℝ,1≤A ∧ 0≤B' ∧ ∀ᶠ i in atTop,
        WilsonMovingForkReporterBothArms.Filed (f:=f) (l:=l) J₀ J c.report d (2*i) A B' ∧
        WilsonMovingForkReporterBothArms.Filed (f:=f) (l:=l) J₀ J c.report d (2*i+1) A B') ∧
      (∀i,WilsonMovingForkReporterNamedInk.Filed B made O χ (X (c.pick i)) (c.report (2*i)) (n₁ (c.pick i)) (z₁ (c.pick i)) ∧
        WilsonMovingForkReporterNamedInk.Filed B made O χ (Y (c.pick i)) (c.report (2*i+1)) (n₂ (c.pick i)) (z₂ (c.pick i))) ∧
      ∀ (torch:ℕ) (need:ℝ), ∀ᶠ i in atTop,
        (need≤(c.report (2*i)).b ∧ torch≤((X (c.pick i)).bag
          (C.path.levels.clock.J (c.report (2*i)).k)).taylor) ∧
        (need≤(c.report (2*i+1)).b ∧ torch≤((Y (c.pick i)).bag
          (C.path.levels.clock.J (c.report (2*i+1)).k)).taylor) :=by
  obtain ⟨c,J,school,radii,wages⟩:=WilsonMovingForkReporterBothArms.original F J₀ lead made simple bliss higher
    lower vanish₁ vanish₂ apart stages₁ stages₂ (fun i=>(sat₁ i).1) (fun i=>(sat₂ i).1)
  have one (i:ℕ) := WilsonMovingForkReporterNamedInk.narrow B made O χ (X (c.pick i))
    (c.outer i) (sat₁ (c.pick i)).2
  have two (i:ℕ) := WilsonMovingForkReporterNamedInk.narrow B made O χ (Y (c.pick i))
    (c.inner i) (sat₂ (c.pick i)).2
  refine ⟨c,J,school,radii,wages,fun i=>?_,fun torch need=>?_⟩
  · rw [even,odd]
    exact ⟨one i,two i⟩
  · obtain ⟨a,ha⟩:=exists_nat_gt need
    filter_upwards [eventually_ge_atTop (max a torch)] with i enough
    have bound (h:ℕ) (hh:i≤h):need≤(h:ℝ)+6:=by
      have ah:a≤h:=(le_max_left ..).trans (enough.trans hh)
      have ar:(a:ℝ)≤h:=by exact_mod_cast ah
      linarith only [ha,ar]
    have first:=c.outer i
    have second:=c.inner i
    rw [even,odd]
    exact ⟨WilsonMovingForkReporterNamedInk.capacity B made O χ _ _ (one i) torch (by omega) (bound _ (by omega)),
      WilsonMovingForkReporterNamedInk.capacity B made O χ _ _ (two i) torch (by omega) (bound _ (by omega))⟩

end YM.Integration.WilsonMovingForkReporterSignedBothArms
end
