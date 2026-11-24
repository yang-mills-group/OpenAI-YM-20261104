import YM.Integration.WilsonThermometerClusterSourceReturn
import YM.Integration.WilsonThermometerUnitFilingSharp

/-! A physical grouped scalar field is filed one original step earlier with its complete regular and forced remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerClusterOlderReading
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical
open Trace.Physical.GermGraph WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFeed
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] [DecidableEq I]
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "C" => R.family
local notation "H" => R.family.path

theorem original (simple:G.Simple) (cater:Cater R.family R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A)) (wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ m:ℕ in atTop,∀ N p:ℕ,m<N →
      let Υ:=R.family.path.rep N p (m+1)
      ∀ (X:Config G ((C).side (m+1) p) → Poly (Stock.census I))
        (g:I → Config G ((C).side (m+1) p)→ℂ) (K:I → ℕ → Config G ((C).side (m+1) p)→ℂ)
        (o:I→Site ((C).side (m+1) p)) (w:I→ℝ),
      Served Υ g (fun v=>profile Υ.activities (K v)) X o w Υ.p.supportExponent 1 →
      (∀ v,Dominated (K v) ∧ Blade Υ (o v) (g v) (profile Υ.activities (K v)) 0 (4*(1/w v))) →
      Integrable X (prior G _) → ∀ v,0<w v → ((A).clock.op m p).ratio.parent (o v)=0 →
      ∀ j : ℕ, (C).ref 0 ≤ j → ∀ (jm : j ≤ m), Opened (C) 0 j p → Opened (C) 0 m p →
        ‖reading R (N:=N) (p:=p) (((A).clock.op m p).push Υ.beta
          (fun U=>(X U).part ((Stock.census I).fire v))) j jm‖ ≤
          (25+24*((A).params m).columns)*(β m)^4*(4*(1/w v)) := by
  filter_upwards [WilsonThermometerClusterSourceReturn.original (I:=I) R simple cater bank wage] with m bill N p edge
  dsimp only
  intro X g K o w table leaves live v pos home j start jm roomJ roomM
  obtain ⟨Q,formatted,paid,size,identity⟩:=bill N p edge X g K o w table leaves live v pos home
  let rem:ℝ:=(β m)^4*(4*(1/w v))
  have hp:0<rem:=by dsimp [rem]; have beta:0<β m:=zero_lt_one.trans (R.family.path.levels.fits.delayed m); positivity
  have coordinate:‖Q.x 0‖≤((C).labels.level 0).coeffSize Q.x:=
    Finset.single_le_sum (f:=fun h=>‖Q.x h‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
  have evidence:=WilsonThermometerUnitFilingSharp.absolute R simple start jm edge.le roomJ roomM rem hp Q formatted paid
  rw [←identity]
  refine evidence.trans ?_
  have sized:‖Q.x 0‖≤rem:=coordinate.trans size
  calc
    _ ≤ rem+2*WilsonMacroscopicRichCaptureFilingBudget.capital (C) m rem rem:=add_le_add_left sized _
    _ = _:=by unfold WilsonMacroscopicRichCaptureFilingBudget.capital rem; ring

end YM.Integration.WilsonThermometerClusterOlderReading
end
