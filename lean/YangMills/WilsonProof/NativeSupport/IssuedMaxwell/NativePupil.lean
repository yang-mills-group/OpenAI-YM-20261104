import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.PositiveCut
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.TriangleCalibration
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.NativePupil
open YM YM.XSpace Function Set
open YangMills.MSbar IssuedMaxwell.Reports
open scoped BigOperators
variable {g:YangMills.GaugeGroup}{V:Normalize.Store g.core}

theorem support (t:RealTest 3):tsupport (fun x=>(t x:ℂ)) ⊆ tsupport t:=by
  apply closure_mono
  intro x nz zero
  exact nz (congrArg Complex.ofReal zero)

def profile (K:Rose.Pick V):Test 3:=
  ⟨fun x=>(K.image x:ℂ),Complex.ofRealCLM.contDiff.comp K.image.contDiff,
    K.image.hasCompactSupport.of_isClosed_subset isClosed_closure (support K.image),
    (support K.image).trans K.image.tsupport_subset⟩

theorem original (K:Rose.Pick V)(nonneg:∀x,0≤K.image x):
    (∀x,0≤(profile K x).re ∧ (profile K x).im=0) ∧
    Rose.Turns (profile K) ∧
    (∀x∈tsupport (profile K),∀a b:Fin 3,a≠b→max 4 (5*K.cut.rOut)<‖x a-x b‖) ∧
    (∫ x, (profile K x).re * YangMills.MSbar.Position.bareTriangle (B g) K.cut x)<0:=by
  refine ⟨fun x=>⟨nonneg x,rfl⟩,fun Q x=>congrArg Complex.ofReal (K.spins Q x),?_,?_⟩
  · intro x hx a b h
    have cut:=K.segment (support K.image hx)
    exact max_lt (Rose.at_spot cut a b h) (cut.1 a b h)
  · apply lt_of_eq_of_lt _ K.fresh
    unfold Rose.cT
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [IssuedMaxwell.TriangleCalibration.graph]
    rfl
end IssuedMaxwell.NativePupil
end
