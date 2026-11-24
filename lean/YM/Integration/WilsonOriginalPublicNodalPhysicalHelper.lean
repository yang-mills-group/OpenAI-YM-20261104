import YM.Integration.WilsonOriginalPublicNodalCommonRaw
import YM.Integration.WilsonOriginalPublicNodalPhysicalNote
import YM.Integration.WilsonOriginalPublicNodalHelperBook

/-! A single bare period, measured at the same physical vector, on both purchased helper sequences. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalPhysicalHelper
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open RegulatorIR.Oracle RegulatorIR.Calibration RegulatorIR.FVAAlt2
open WilsonIndependentEvenPassport (power)
open WilsonOriginalPublicNodalHelperShape (length physical)
open WilsonOriginalPublicNodalCommonRaw (Court)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{X:Type}{M:X → ℕ}{n:Page M → Side}{K:KernelChoices}

def court (C:Circuit M n)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(F:Tent M)(L:Meter X)
    (cash:Flap M → ℝ≥0∞)(p b u:ℕ)(D:Choice M)(γ:ℝ)
    (paid:let T:=C.lane Y G Z (sheet F)
      Cylinder T (C.payroll Y G Z (sheet F)) (C.pushP Y G) (C.takeP Y G) L cash p b u ∧
        Lantern (C.dialect Y G Z (sheet F)) D L cash γ ∧ T.Endings L)
    (unit:∀x,C.l (Page.opening _ x)=1)(flat:∀x,sheet F (Page.opening _ x)=Clocks.flat):Court G X p:=
  ⟨M,n,C.dialect Y G Z (sheet F),C.lane Y G Z (sheet F),C.payroll Y G Z (sheet F),C.pushP Y G,C.takeP Y G,
    L,cash,b,u,D,γ,paid.1,paid.2.1,paid.2.2,C.passage Y G Z (sheet F),fun _=>rfl,unit,flat⟩

variable (V:XSpace.Run)(m j:X → ℕ)(w:X → ℕ → ℕ)
def period (x:X):XSpace.Period:=
  ⟨V.finalSide.side*power V (physical j w x),dvd_mul_of_dvd_left V.finalSide.even _,
    V.finalSide.large.trans (Nat.le_mul_of_pos_right _ (V.den_pos _))⟩

def sample (x:X)(mesh:ℝ)(h:0 < mesh)(z:Fin 2 → Cover)(c:Room):Sample 2:=
  ⟨⟨period V j w x,mesh,h⟩,z,c⟩

theorem sides (r:X → ℕ)(a:ℕ)(enough:∀x,r x ≤ physical j w x)(x:X):
    let E:=physical j w
    let P:=period V j w x
    TopF (WilsonPositionProgramInfraredCircuit.count V j w) x=P.side ∧
      TopF (WilsonOriginalPublicNodalHelperShape.n V E r a) x=P.side:=by
  exact ⟨rfl,WilsonOriginalPublicNodalHelperShape.opening V (physical j w) r a enough x⟩

end YM.Integration.WilsonOriginalPublicNodalPhysicalHelper
end
