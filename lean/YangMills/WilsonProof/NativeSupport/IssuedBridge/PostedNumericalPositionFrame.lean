import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNumericalAdjustment
import YM.Integration.WilsonPositionHomogeneousFrame
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedNumericalPositionFrame
open YangMills YangMills.Wilson YM YM.Integration Maxwell Maxwell.Free XSpace XSpace.Normalize
open Lattice Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS
open FVA2 FVA2.Register FVA2.Scale WilsonPositionHomogeneousCoefficients
open Function Filter Set
open scoped Topology BigOperators Classical
variable {g : GaugeGroup} {R : Run g.core} {order : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family order S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription g.core) (law : Warrant Z)

theorem original {r : ℝ} (d : ℕ) (heat : 0 < WilsonPositionHomogeneousFrame.reading F J Z r)
    (fit : Bijective ((PostedNumericalAdjustment.filed Z law).value d (WilsonPositionHomogeneousFrame.reading F J Z r)))
    (v : (maxwellReference g).sector d) :
    WilsonPositionHomogeneousFrame.homogeneous F J Z r d ((fields R.family.labels d).symm v) =
      WilsonPositionPrescribedFrame.positioned F J Z.store r d ((fields R.family.labels d).symm
        ((PostedNumericalAdjustment.filed Z law).value d (WilsonPositionHomogeneousFrame.reading F J Z r) v)) := by
  have eq : (PostedNumericalAdjustment.filed Z law).value d (WilsonPositionHomogeneousFrame.reading F J Z r) =
      stand (WilsonPositionHomogeneousFrame.turn F J Z d r) := by
    rw [PostedNumericalAdjustment.original Z law d heat]
    simp only [WilsonPositionHomogeneousFrame.turn,WilsonPositionHomogeneousNear.field,if_pos heat]
  rw [eq] at fit ⊢
  have leg (z : Sec g.core d) : WilsonPositionHomogeneousFrame.change F J Z d r ((fields R.family.labels d).symm z) = (fields R.family.labels d).symm (stand (WilsonPositionHomogeneousFrame.turn F J Z d r) z) := by
    unfold WilsonPositionHomogeneousFrame.change
    split
    · simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply]
    · rename_i denied
      exact (denied fit).elim
  exact congrArg (WilsonPositionPrescribedFrame.positioned F J Z.store r d) (leg v)

theorem appointed (clock : Tendsto (WilsonPositionHomogeneousFrame.reading F J Z) trail (𝓝[>] 0)) (d : ℕ) :
    ∀ᶠ r : ℝ in trail, ∀ v : (maxwellReference g).sector d,
    WilsonPositionHomogeneousFrame.homogeneous F J Z r d ((fields R.family.labels d).symm v) =
      WilsonPositionPrescribedFrame.positioned F J Z.store r d ((fields R.family.labels d).symm
        ((PostedNumericalAdjustment.filed Z law).value d (WilsonPositionHomogeneousFrame.reading F J Z r) v)) := by
  filter_upwards [clock.eventually (self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)),
    clock.eventually ((PostedNumericalAdjustment.filed Z law).invertible d)] with r pos fit
  exact original F J Z law d pos fit
end IssuedBridge.PostedNumericalPositionFrame
