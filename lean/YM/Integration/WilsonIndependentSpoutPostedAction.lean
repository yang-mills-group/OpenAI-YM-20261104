import YM.Integration.WilsonIndependentSpoutPrimitiveReport
import YM.Integration.WilsonIndependentSpoutThermalMark

/-! The real signed finite coefficient table, as an actual polynomial
before Wick integration on the same cut. No test-dependent representation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPostedAction
open Matrix PowerSeries Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Prim RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Clocks.Warp
open RegulatorIR.Calibration RegulatorIR.Ward Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentPublicFreeTrain
open WilsonIndependentSpoutPrimitiveReport (axis)
open WilsonIndependentSpoutFiniteStencil (Raw)
open WilsonIndependentSpoutOrdinaryPrimitives (board)
open scoped Classical BigOperators Matrix
variable {G:Gauge}

def seat (n:Side)(z:Raw G n):Woods G n:=ix (z.1.1,coord z.1.2) z.2

def print (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))(e:ℕ):POL (Joint G (n*P.L) n):=
  MvPolynomial.rename (Sum.map (seat (n*P.L)) (seat n)) (packed (board P n T e) (e+2))

theorem heard (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))(e:ℕ)(z:Lawn (Joint G (n*P.L) n)):
    MvPolynomial.eval z (print P n T e)=drums (board P n T e) (e+2) (Sum.elim (axis (leftArm z)) (axis (rightArm z))):=by
  rw [print,MvPolynomial.eval_rename,←speaking]
  congr 1
  funext v;cases v <;>rfl

private theorem compare {P Q:Patch}{n:Side}(eq:Q=P)(T:Branchix→Orders (KFoot G))(e:ℕ)
    (u:TreeVars G (n*Q.L))(b:TreeVars G n):
    drums (board Q n T e) (e+2) (Sum.elim (axis u) (axis b))=
      drums (board P n T e) (e+2) (Sum.elim (axis ((congr_arg (fun X:Patch=>TreeVars G (n*X.L)) eq) ▸ u)) (axis b)):=by
  subst P;rfl

def coefficient (A:Levels G)(N m:ℕ)(n:Side)(T:Branchix→Orders (KFoot G))(α:Cost)(V:PChart G (n*(loose A m).L))(e:ℕ):=
  let S:=mStep A n m;let F:=repeatF S;let Q:=extractV G S F (roam A N m n)
  let H:=freeForms A N (m+1)
  cord (camSlice G S F Q) (coeff e (orbC (precisionC G _ H)-flash (mix α V)))+
    cord (panSlice G S F Q) (print (loose A m) n T e)

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(s:ℕ)(inc:Matches A C K s f.volW)

include Y inc in
theorem original (n:Side)(e:ℕ)(he:0<e):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1))
    let S:=mStep A n m;let F:=repeatF S;let Q:=roam A N m n
    let H:=freeForms A N (m+1);let H':=freeForms A N m;let α:=tale (D f.prev).dine
    let Ñ:=XSpace.Bare.chart G;let T:=C.bore G Z (sheet D) f;let V:=(story A Ñ N (m+1)).1 (n*(loose A m).L)
    coefficient A N m n T α V e=coeff e (WilsonIndependentSpoutSchurFrame.field S F H H' Q α Ñ V):=by
  intro N m S F Q H H' α Ñ T V
  apply MvPolynomial.funext
  intro x
  have physical:=WilsonIndependentSpoutPrimitiveReport.original C Y Z D f A s inc n e he x
  dsimp only at physical
  let z:=overM G S F *ᵥ x
  let u:=camber G (extractV G S F Q) *ᵥ z
  let b:=rightArm z
  have cu:camSlice G S F (extractV G S F Q) *ᵥ x=u:=by rw [camSlice,←Matrix.mulVec_mulVec]
  have cb:panSlice G S F (extractV G S F Q) *ᵥ x=WilsonIndependentSpoutOrdinarySpring.tuple u b:=by
    rw [panSlice,←Matrix.mulVec_mulVec]
    ext j;cases j with
    | inl j=>exact congr_fun (camIn G (extractV G S F Q) z).1 j
    | inr j=>exact congr_fun (camIn G (extractV G S F Q) z).2 j
  rw [coefficient,map_add,cord_apply,cord_apply,heard,cu,cb]
  change _+drums (board (loose A m) n T e) (e+2) (Sum.elim (axis u) (axis b))=_
  rw [compare (Q:=loose A m) (P:=C.pactP f) (inc.patches f rfl) T e u b]
  exact physical.symm

end YM.Integration.WilsonIndependentSpoutPostedAction
