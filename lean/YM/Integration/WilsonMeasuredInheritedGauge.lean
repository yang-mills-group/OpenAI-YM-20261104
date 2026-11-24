import YM.Integration.WilsonHeldAcceptedCovariance
import YM.UVNext.PHASE_COARSE_ERROR.Marginal

/-! Gauge invariance of the full earlier complex observable under the
actual normalized Wilson transport, including the complete previous action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredInheritedGauge
open MeasureTheory Lattice RG Wilson Push.SectorMeasure
open private sampled from YM.Integration.WilsonCenteredHaarReading
open scoped Classical
variable {G:Gauge} (C:Family G) (makes:C.Makes) {N per j b:ℕ}

include makes

theorem original (top:b≤N) (live:j≤b) (A:Config G (C.side b per)→ℂ)
    (ha:Envelope A) (gi:GaugeInvariant A) :
    let F:=actualTransport C (N:=N) A live
    Envelope F ∧ GaugeInvariant F := by
  induction live using Nat.decreasingInduction with
  | self=>rw [actualTransport_base C makes top];exact ⟨ha,gi⟩
  | of_succ i hi ih=>
    rw [actualTransport_step C makes top _ hi]
    let F:=actualTransport C (N:=N) A (Nat.succ_le_of_lt hi)
    let Z:=C.path.rep N per (i+1)
    let S:=C.path.levels.clock.op i per
    have next:=hi.trans_le top
    have ez:=Z.envelope (makes.wilson.represents N per (i+1) next).good
    have gz:=Presented.lawful_gi (makes.wilson.represents N per (i+1) next).good
    have gD:=Presented.lawful_gi (makes.wilson.represents N per i next.le).good
    have grow:GaugeInvariant (fun U=>Z.eval U • F U):=by
      intro t U;exact congrArg₂ (· • ·) (gz t U) (ih.2 t U)
    have send:=UVNext.PhaseCoarse.push_invariant S (C.path.levels.blocks i per).branches
      (C.path.β N per (i+1)) (fun U=>Z.eval U • F U) (sampled _ (ez.integrable _) ih.1) grow
    refine ⟨WilsonForwardMeasurable.average makes next ih.1,?_⟩
    intro t V
    exact (actualAverage_push C F (Lattice.gauge t V)).trans
      ((congrArg₂ (· • ·) (congrArg (fun x:ℝ=>x⁻¹) (gD t V)) (send t V)).trans
        (actualAverage_push C F V).symm)

theorem occupied (live:j≤N) (v:C.label 4) (x:Site (C.side N per)):
    let F:=actualTransport C (N:=N) (C.O N per v x) live
    Envelope F ∧ GaugeInvariant F :=
  original C makes le_rfl live _ (Env.compact (C.continuousO N per 4 v x))
    (C.invariant makes N per 4 v x)

end YM.Integration.WilsonMeasuredInheritedGauge
end
