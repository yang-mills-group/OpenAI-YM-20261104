import YM.Integration.WilsonIndependentNotebookOrdinaryProduct

/-! The occupied joint reading on the true selected edge, with its incoming
connected part and its new conditional covariance retained separately. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookOrdinaryBirth
open Function PowerSeries Lattice Laurent RG RegulatorIR RegulatorIR.Prim RegulatorIR.Calibration RegulatorIR.Diagram RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonIndependentNotebookPayrollMark (source)
open WilsonIndependentNotebookMarkedEdge (Reads)
open WilsonIndependentNotebookOrdinaryProduct (product)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
variable (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(A:W→Levels G)(s:W→ℕ)

theorem original (simple:G.Simple)(p:ℕ)(f:Flap M)(funded:Reads C Y Z D A s p f)
    {i j:ℕ}{X V H:Era G ℝ}(x:Auth i X)(v:Auth j V)(h:Auth (i+j) H):
    let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1));let Ñ:=XSpace.Bare.chart G
    let emit (k:ℕ)(U:Era G ℝ):=(C.devices Y G Z (sheet D) f).each k
       ((C.payroll Y G Z (sheet D)).bulk f.prev) (source A s f.prev U)
    RegulatorIR.Clocks.Matches p (emit (i+j) H-product (emit i X) (emit j V))
       (source A s f.next (verseI (A f.volW) Ñ m N (i+j) (H-agateV X V)+
          JoinGap (A f.volW) Ñ m N i j X V)):=by
  intro N m Ñ emit
  have ht:m<N:=by have:=f.ok;dsimp only [m,N];omega
  have ratio:=XSpace.Bare.chart_ratio G
  have right:=WilsonIndependentNotebookOrdinaryProduct.preserves (funded i X x) (funded j V v)
  have exact_old:verseI (A f.volW) Ñ m N (i+j) (H-agateV X V)+JoinGap (A f.volW) Ñ m N i j X V=
     verseI (A f.volW) Ñ m N (i+j) H-agateV (verseI (A f.volW) Ñ m N i X) (verseI (A f.volW) Ñ m N j V):=by
    unfold JoinGap
    rw [verse_lin (A f.volW) simple ht ratio h (x.manor v)]
    abel
  rw [exact_old,WilsonIndependentNotebookOrdinaryProduct.subtract]
  intro e he
  change emit (i+j) H e-product (emit i X) (emit j V) e=source _ _ _ _ e-source _ _ _ _ e
  rw [show emit (i+j) H e=_ from funded (i+j) H h e he,
    show product (emit i X) (emit j V) e=_ from right e he]
  rw [WilsonIndependentNotebookOrdinaryProduct.restores A s f.next
    (Auth.verse (A f.volW) ht simple ratio x) (Auth.verse (A f.volW) ht simple ratio v)]

end YM.Integration.WilsonIndependentNotebookOrdinaryBirth
