import YM.Integration.WilsonIndependentNotebookPayrollMark
import YM.Integration.WilsonIndependentSpoutRealMarkRows

/-! A normalized marked Wilson step on the same notebook as the entire
unmarked Wilson history. The mark and every translated input can be supplied
after choosing the notebook. The equality includes its occupied scalar. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookMarkedEdge
open Function Matrix PowerSeries Lattice Laurent RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Calibration
open RegulatorIR.Diagram RegulatorIR.Ward
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonIndependentSpoutFundedClocks (age clock)
open WilsonIndependentSpoutPayrollRoute (reported)
open WilsonIndependentNotebookPayrollMark (source)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
variable (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(A:W→Levels G)(s:W→ℕ)

def Reads (p:ℕ)(f:Flap M):Prop:=
  let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1))
  ∀(k:ℕ)(X:Era G ℝ),Auth k X→RegulatorIR.Clocks.Matches p
    ((C.devices Y G Z (sheet D) f).each k ((C.payroll Y G Z (sheet D)).bulk f.prev) (source A s f.prev X))
    (source A s f.next (verseI (A f.volW) (XSpace.Bare.chart G) m N k X))

theorem original (simple:G.Simple)(p:ℕ)(f:Flap M)(R:WilsonIndependentPublicFreeTrain.Matches (A f.volW) C K (s f.volW) f.volW)
    (prior:RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk f.prev) (reported A s f.prev))
    (clocked:Squares p (tale (D f.prev).dine) (clock A (XSpace.Bare.chart G) s f.prev))
    (paid:∀n,WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f (A f.volW) (s f.volW) p n):
    Reads C Y Z D A s p f:=by
  unfold Reads; dsimp only; intro k X auth
  apply WilsonIndependentNotebookPayrollMark.issued C Y Z D A s simple p f R prior clocked k X auth
  intro e he r n
  exact congrFun (WilsonIndependentSpoutRealMarkRows.original C Z D f (A f.volW) (s f.volW) simple p n
    (paid n) X auth e he) r

theorem selected (simple:G.Simple)(inc:∀w,WilsonIndependentPublicFreeTrain.Matches (A w) C K (s w) w)(p:ℕ):
    let Ñ:=XSpace.Bare.chart G
    ∃D:Tent M,(∀c:G.ColorIndex,Notebook C Y G Z c (RegulatorIR.FVAAlt2.Rocket.native M) D p) ∧
      (∀v,RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk v) (reported A s v)) ∧
      (∀v,Squares p (tale (D v).dine) (clock A Ñ s v) ∧
         Squares p (tale (sheet D v).beta) (((clock A Ñ s v)⁻¹)^2)) ∧
      (∀(f:Flap M)(n:Side),WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f (A f.volW) (s f.volW) p n) ∧
       ∀f,Reads C Y Z D A s p f:=by
  intro Ñ
  obtain ⟨D,books,prior,bill,paid⟩:=WilsonIndependentSpoutEarnedNotebook.original C Y Z A s simple inc p
  exact ⟨D,books,prior,bill,paid,fun f=>original C Y Z D A s simple p f (inc _) (prior _) (bill _).1 (paid f)⟩

end YM.Integration.WilsonIndependentNotebookMarkedEdge
