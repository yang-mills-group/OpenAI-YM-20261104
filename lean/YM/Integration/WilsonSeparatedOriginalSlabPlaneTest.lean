import YM.Integration.WilsonSeparatedOriginalSlabCenterBill
import YM.RG05Readout.Pulse.Groups

/-! Every original incident multi-jet of a separated spatial frequency retains the one common centre phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabPlaneTest
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native RG05Readout.Pulse
open WilsonSeparatedOriginalSlabCenterPhase
open private right from YM.Integration.WilsonSeparatedOriginalSlabCenterPhase
open scoped BigOperators Classical Topology ContDiff
variable {I:Type}[Fintype I]

def body (v:Axis→ℝ)(c:ℝ):Body:=⟨fun z=>mode v (c • z),by
  change ContDiff ℝ ∞ (fun z:E4=>mode v (c • z))
  unfold mode
  have scalar:ContDiff ℝ ∞ (fun z:E4=>∑ d,v d*(c • z) d):=by fun_prop
  have complex:ContDiff ℝ ∞ (fun z:E4=>((∑d,v d*(c • z) d:ℝ):ℂ)):=Complex.ofRealCLM.contDiff.comp scalar
  fun_prop⟩

def packet (v:I→Axis→ℝ)(c:ℝ):Wave I:=joint Finset.univ (fun i=>body (v i) c)

theorem character (v:I→Axis→ℝ)(c:ℝ)(x:Cloud I):
    fork (1:ℝ) x (packet v c)=(packet v c).val x • packet v c:=by
  apply Subtype.ext; funext y
  change (∏i,mode (v i) (c • (x+1 • y) i))=(∏i,mode (v i) (c • x i))*(∏i,mode (v i) (c • y i))
  simp only [one_smul,Pi.add_apply,smul_add,right,Finset.prod_mul_distrib]

theorem dilation (v:I→Axis→ℝ)(c:ℝ):packet v c=fork c 0 (packet v 1):=by
  apply Subtype.ext; funext y
  change (∏i,mode (v i) (c • y i))=∏i,mode (v i) (1 • (0+c • y) i)
  simp

variable [DecidableEq I] (s:I→ℕ)(k:(i:I)→Letter (s i))
local notation "deg"=>pegs s k (Finset.univ.toList)

theorem translated (v:I→Axis→ℝ)(c:ℝ)(x:Cloud I):
    (perform s k (packet v c)).val x=(packet v c).val x*(perform s k (packet v c)).val 0:=by
  calc
    _=(perform s k (fork (1:ℝ) x (packet v c))).val 0:=by
      unfold perform; rw [machine_roll]; simp [fork]
    _=_:=by rw [character,map_smul]; rfl

theorem derivative (v:I→Axis→ℝ)(c:ℝ)(x:Cloud I):
    (perform s k (packet v c)).val x=(packet v c).val x*(c:ℂ)^deg*(perform s k (packet v 1)).val 0:=by
  rw [translated s k v c x,mul_assoc]
  apply congrArg ((packet v c).val x * ·)
  rw [dilation v c]
  unfold perform; rw [machine_roll]
  simp [fork]

end YM.Integration.WilsonSeparatedOriginalSlabPlaneTest
