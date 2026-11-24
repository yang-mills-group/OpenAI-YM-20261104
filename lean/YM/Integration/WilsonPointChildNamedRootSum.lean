import YM.WilsonCoeffUV.Marked.Capture.Draw
import YM.Integration.WilsonPointChildPlacedFold
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildNamedRootSum
open YM Lattice WilsonCoeffUV RG FormalBulk08 Laurent
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open Work.F08 Function Finset Filter
open scoped Classical BigOperators Topology
variable {ι α V:Type} [DecidableEq ι] [Fintype α]
variable [NormedAddCommGroup V]{r:ℕ}

theorem original (I:Finset ι)(o:ι)(live:o∈I)(root:Cover)(w A:ℝ)(pos:0<w)(credit:0≤A)
    (K:(ι → Cover) → dock Cover α r → V)(bought:∀p,Wig terrain p w A I (K p)):
    SumBudget (fun f:Fence α I o r=>
      Real.exp ((w/2)*Syn terrain (toe I o root f.1) I f.2)*‖K (toe I o root f.1) f.2‖)
      (A*(tiePay Unit (Fintype.card (I.erase o)) ((2*w)/8)*tiePay α r ((2*w)/8))):=by
  have raw:=sprig_both (α:=α) live root (show 0<2*w by positivity) r
  apply budget_minor (cap_scale raw credit) (fun _=>by positivity)
  intro f
  let p:=toe I o root f.1
  let span:ℝ:=Syn terrain p I f.2
  change Real.exp (w/2*span)*‖K p f.2‖ ≤ A*Real.exp (-(2*w/4)*span)
  have atTerm:‖K p f.2‖≤A*Real.exp (-w*span):=(bought p).2 _
  calc _ ≤ Real.exp (w/2*span)*(A*Real.exp (-w*span)):=mul_le_mul_of_nonneg_left atTerm (Real.exp_pos _).le
       _ = A*Real.exp (-(2*w/4)*span):=by rw [←mul_left_comm,←Real.exp_add];congr 2;ring

end YM.Integration.WilsonPointChildNamedRootSum
