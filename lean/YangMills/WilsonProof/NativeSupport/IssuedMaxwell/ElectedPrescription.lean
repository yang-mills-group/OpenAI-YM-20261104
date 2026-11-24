import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.NativeMenu
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.AppointedPrescription
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.ElectedPrescription
open YM YM.Integration YM.FVA2 YM.FVA2.Register YM.XSpace YangMills.MSbar
variable (g:YangMills.GaugeGroup)
theorem simple (h:g.IsSimple):g.core.Simple:=by
  have eq : g.core.lie=g.lieAlgebra:=SetLike.ext fun x=>(g.generates x).symm
  unfold Gauge.Simple
  rw [eq]
  exact h

def prior (h:g.IsSimple):{P:PositionPrescription (Reference.issued g)//Admissible P}:=
  NativeMenu.registered g (simple g h)

def issued (h:g.IsSimple):WilsonPrescription g.core:=
  AppointedPrescription.issued (simple g h) (prior g h).1 (prior g h).2

theorem original (h:g.IsSimple):
    (issued g h).run=AppointedPrescription.ternary ∧
    (issued g h).store=PositionStore.original (prior g h).1 (prior g h).2 ∧
    (issued g h).criterion.cut=(prior g h).1.triangle.cut ∧
    (∀x,((issued g h).criterion.image x:ℂ)=(prior g h).1.triangle.profile x) ∧
    (∀dial:Bool,∃σ,Main.Match (issued g h) (simple g h)
        (WilsonCapturedPhysicalMSDatum.original g.core) σ dial):=by
  obtain ⟨run,store,_,cut,image,_,matched⟩:=
    AppointedPrescription.original (simple g h) (prior g h).1 (prior g h).2
  exact ⟨run,store,cut,image,matched⟩
end IssuedMaxwell.ElectedPrescription
end
