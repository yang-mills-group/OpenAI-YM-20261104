import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.ElectedMaxwellInputs
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.PublishedFrameTransfers
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Answer.ContinuumLimit.ElectedMaxwellLaws
open Function Filter Set Integration Integration.Election Lattice RG Wilson Extraction Climb Spec
open Trace.Pilot PhysicalNext.Repeat.Legato OPE OPE.Orbits PhysMS PhysMS.Frame XSpace XSpace.Normalize FVA2 FVA2.Register
open scoped Topology BigOperators Classical
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ} {e : Axis} {O : OrderS g.core}
  {E : Construction.{u} H ε e O} {ξ : Extraction.Order}

def publicFrame (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) :
    YangMills.AllRadii.Frame (YangMills.maxwellReference g) (YangMills.hierarchy V.pupil.last V.pupil.P) :=
  fun d => (YM.Maxwell.Free.fields E.paths.family.labels d).symm.trans (V.Post Z r d)

def occupied (V : Vision E ξ) (Z : WilsonPrescription g.core) : Prop :=
  ∀ i j : Axis, Tendsto (fun r : ℝ => (V.Post Z r 4).symm (r^4 • V.pupil.last.sector.energy i j))
    trail (𝓝 (Pert.freeStress E.paths.family.labels i j))

def laws (V : Vision E ξ) (Z : WilsonPrescription g.core) : Prop :=
  let B := YangMills.maxwellReference g
  let T := YangMills.hierarchy V.pupil.last V.pupil.P
  ∃ X : T.MaxwellScaling B, YangMills.FixedFields.Laws B T X ∧
    YangMills.AllRadii.Laws B T X (publicFrame V Z) ∧ YangMills.AllRadii.FrameBounds B T X (publicFrame V Z)

theorem atRadii (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool}
    (Q : Perspective H Z lamp) (radii : Climb.Scaling V.pupil.S) (stress : occupied V Z) : laws V Z := by
  let source : PublishedMixedMaxwell.Inputs V.pupil.last V.pupil.P V.pupil.J V.pupil.H Z H :=
    { facilities := V.pupil.pillar
      leading := V.pupil.VFrame.2
      obeys := V.pupil.VFrame.1
      viewer := @fun n d v j K hK sep δ pos => PublishedFrameTransfers.viewerZero V Z Q v j K hK sep δ pos
      stress := stress }
  exact YangMills.PublishedFrameLaws.original Z source radii

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) {lamp : Bool}
    (Q : Perspective H Z lamp) (stress : occupied V Z) : laws V Z := by
  obtain ⟨_, _, radii, _, _⟩ := V.pupil.bliss.picks (fun n : ℕ => 1 / ((n:ℝ) + 1))
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => by positivity)
  exact atRadii V Z Q radii stress

end YM.Answer.ContinuumLimit.ElectedMaxwellLaws
end
