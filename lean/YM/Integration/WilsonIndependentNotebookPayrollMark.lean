import YM.Integration.WilsonIndependentNotebookMarkedReceiver
import YM.Integration.WilsonIndependentSpoutEarnedNotebook

/-! The finite trial at the paid notebook's actual incoming vacuum and the
actual two successive numerical coupling charts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookPayrollMark
open Function Matrix PowerSeries Lattice Laurent RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Diagram RegulatorIR.Ward RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Calibration
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonIndependentConditionalNativeLinks (coarse)
open WilsonIndependentConditionalCoordinateHeat (orders ranks)
open WilsonIndependentSpoutFundedClocks (age clock)
open WilsonIndependentSpoutPayrollRoute (reported)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
variable (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(A:W→Levels G)(s:W→ℕ)

def source (v:Page M)(X:Era G ℝ):Orders (Foot G):=
  orders (coarse G) (mix (clock A (XSpace.Bare.chart G) s v) X.2)

theorem issued (simple:G.Simple)(p:ℕ)(f:Flap M)(R:WilsonIndependentPublicFreeTrain.Matches (A f.volW) C K (s f.volW) f.volW)
    (paid:RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk f.prev) (reported A s f.prev))
    (bill:Squares p (tale (D f.prev).dine) (clock A (XSpace.Bare.chart G) s f.prev))
    (k:ℕ)(X:Era G ℝ)(auth:Auth k X):
    let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1));let Ñ:=XSpace.Bare.chart G
    let β:=relativeC (A f.volW) Ñ N m (N-m);let V:=verseI (A f.volW) Ñ m N k X
    (∀e≤p,∀r n,WilsonIndependentNotebookMarkHear.output C Z D f (A f.volW) (s f.volW) k X n e r=
      mix β (V.1 n) e r)→
    RegulatorIR.Clocks.Matches p ((C.devices Y G Z (sheet D) f).each k
      ((C.payroll Y G Z (sheet D)).bulk f.prev) (source A s f.prev X)) (source A s f.next V):=by
  intro N m Ñ β V finite
  let α:=tale (D f.prev).dine
  have hf:=f.ok
  have upper:age s f.prev=m+1:=by change s f.volW+(M f.volW-f.offset)=_;dsimp only [m];omega
  have unit:constantCoeff (clock A Ñ s f.prev)=1:=by
    apply angularC simple (XSpace.Bare.chart_ratio G)
    have h:=f.prev.good;unfold age;omega
  have vacuum:RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk f.prev)
      (WilsonIndependentSpoutReportedQuiet.port (A f.volW) Ñ N (m+1) α):=by
    intro i hi
    have h:=WilsonIndependentSpoutPayrollSeeds.clock (A f.volW) Ñ N (age s f.prev) bill unit i hi
    exact (paid i hi).trans (upper ▸ h.symm)
  have mark(i)(hi:i≤p):source A s f.prev X i=ranks (coarse G) (mix α X.2 i):=by
    apply congrArg (ranks (coarse G))
    exact (WilsonIndependentSpoutClockedPrint.source bill unit X.2 hi).symm
  have lower:N-m=f.offset+1:=by dsimp only [m,N];omega
  intro e he;ext1 r
  have heard:=WilsonIndependentNotebookMarkedReceiver.issued C Y Z D f (A f.volW) (s f.volW) R simple k X auth
    p e r he (finite e he r) _ _ (fun i hi j _=>congrFun (vacuum i hi) j) mark
  change _=orders (coarse G) (mix β V.2) e r at heard
  unfold β at heard
  rw [lower] at heard
  exact heard

end YM.Integration.WilsonIndependentNotebookPayrollMark
