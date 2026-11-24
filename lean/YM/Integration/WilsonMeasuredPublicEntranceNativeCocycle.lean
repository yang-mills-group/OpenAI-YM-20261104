import YM.Integration.WilsonMeasuredPublicEntranceNativeParity
import YM.Integration.WilsonMeasuredPublicEntranceDatedGauge
import YM.Integration.WilsonMovingForkReporterBraided

/-! The two previously appointed original home charts give the dated operator on the selected course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeCocycle
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE Spin
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Further.CorrectedLift
open WilsonMeasuredPublicEntranceNativeFrame WilsonMovingForkReporterBraided
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (ℓ:Ultrafilter (ℕ×ℕ)){radius:ℝ}(horizon:Set.Ioc (0:ℝ) radius→ℕ)
    (survey:∀s,Vane C (horizon s))(fallback:ℝ→tower S)
    (outer inner:ℕ→Set.Ioc (0:ℝ) radius)
    (chosen:Pair (fun i=>survey (outer i)) (fun i=>survey (inner i)))
    {J:Scaling S}{H:(Cells.standard C).Hierarchy}
    {Y:∀d:ℕ,ℕ→(Cells.standard C).Field d→L[ℂ] C.label d}

theorem original (income:Gondola f H J ℓ chosen.report Y)(d:ℕ):
    ∀ᶠ i:ℕ in atTop,
      let r:ℝ:=outer (chosen.pick i)
      let t:ℝ:=inner (chosen.pick i)
      let positive:0<t/r:=div_pos (inner (chosen.pick i)).property.1 (outer (chosen.pick i)).property.1
      ∀v:(Cells.standard C).Field d,
        Frame.cocycle d (atRadius ℓ horizon survey fallback) r (t/r) positive v=
        (Pert.Scale.gearIso C.labels d (t/r) positive).symm
          ((J.U (2*i) d).symm (J.U (2*i+1) d v)):=by
  filter_upwards [WilsonMeasuredPublicEntranceNativeParity.original ℓ horizon survey fallback
    outer inner chosen income d] with i gauges
  dsimp only
  intro v
  simp only [Frame.cocycle,LinearEquiv.trans_apply,div_mul_cancel₀ _
    (ne_of_gt (outer (chosen.pick i)).property.1),gauges.1,gauges.2]

end YM.Integration.WilsonMeasuredPublicEntranceNativeCocycle
end
