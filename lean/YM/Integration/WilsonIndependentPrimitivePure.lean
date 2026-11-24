import YM.Integration.WilsonIndependentPrimitiveGranted

/-! The full folded primitive respects polarization before the choice of an external ray. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPrimitivePure
open Function Filter Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Oracle RegulatorIR.Profiles
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Diagram RegulatorIR.Budget
open RegulatorIR.Budget.Packet RegulatorIR.Halo RegulatorIR.Binding RegulatorIR.Calibration
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonIndependentSpoutFiniteStencil (Keys fold)
open WilsonIndependentSpoutOrdinaryPrimitives (liftKey)
open WilsonIndependentPrimitiveCoordinates (printed jo)
open scoped BigOperators Classical

def reorder {I X:Type}(V:Equiv.Perm I):Equiv.Perm (I→X):={
  toFun:=fun x=>x∘V
  invFun:=fun x=>x∘V.symm
  left_inv:=fun x=>funext fun j=>congr_arg x (V.apply_symm_apply j)
  right_inv:=fun x=>funext fun j=>congr_arg x (V.symm_apply_apply j) }

theorem folded {I X Y:Type}(π:X→Y)(u:(I→X)→ℝ)(h:∀(v:Equiv.Perm I) z,u (z∘v)=u z)
    (v:Equiv.Perm I)(z:I→Y):
    Stalk.collect (fun a:I→X=>π∘a) u (z∘v)=Stalk.collect (fun a:I→X=>π∘a) u z:=by
  have w:=WilsonIndependentPrimitiveOrbit.collect (fun a:I→X=>π∘a)
    (reorder (X:=X) v) (reorder (X:=Y) v) (fun _=>rfl) u z
  have eq:u∘(reorder v).symm=u:=funext fun i=>h v.symm i
  rw [eq] at w;exact w

theorem original {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}(C:Circuit M sides)
    (Z:∀P:Patch,P.Branches K G)(t:Page M→Scale)(f:Flap M)(n:Side)(e:ℕ):
    Pure (fun r=>printed (C.pactP f) (C.bore G Z t f) e r n):=by
  intro r s x
  let P:=C.pactP f;let T:=C.bore G Z t f
  simp only [printed,WilsonIndependentSpoutOrdinaryPrimitives.board,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact folded (fold P n) (T (liftKey i) e r) ((C.wheeled G Z t f (liftKey i)).smooth e r) s ((jo G P n).symm∘x)

end YM.Integration.WilsonIndependentPrimitivePure
