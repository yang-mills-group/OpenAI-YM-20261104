import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
import YM.Integration.WilsonCapturedPhysicalMSDatum
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.AppointedPrescription
open YM YM.Integration YM.FVA2 YangMills.MSbar
open XSpace XSpace.Normalize FVA2.Register FVA2.Register.WilsonPrescription

def ternary:XSpace.Run:=⟨3,by decide,1,⟨4,by decide,by decide⟩,by decide,by decide⟩
variable {g:YangMills.GaugeGroup}(simple:g.core.Simple)
variable (P:PositionPrescription (Reference.issued g))(H:Admissible P)

private theorem seed (h:g.core.Simple) : ∃N:WilsonPrescription g.core,N.run=ternary:=by
  obtain ⟨N,_,_,paid,_⟩:=Main.solution g.core h ternary false
  exact ⟨N,paid⟩

def issued : WilsonPrescription g.core:=
  {(seed simple).choose with store:=PositionStore.original P H,criterion:=CalibratedStore.issued simple P H}

theorem original :
    (issued simple P H).run=ternary ∧ (issued simple P H).store=PositionStore.original P H ∧
    HEq (issued simple P H).criterion (CalibratedStore.issued simple P H) ∧
    (issued simple P H).criterion.cut=P.triangle.cut ∧
    (∀x,((issued simple P H).criterion.image x:ℂ)=P.triangle.profile x) ∧
    Rose.cT (issued simple P H).criterion.cut g.core (issued simple P H).criterion.image=P.triangle.cT ∧
    ∀dial:Bool,∃σ,Main.Match (issued simple P H) simple
      (WilsonCapturedPhysicalMSDatum.original g.core) σ dial:=
  ⟨(seed simple).choose_spec,rfl,HEq.rfl,rfl,(NegativePupil.original P H).2.2,
    TriangleCalibration.price g P,Main.wilson_to_MS _ simple _⟩
end IssuedMaxwell.AppointedPrescription
end
