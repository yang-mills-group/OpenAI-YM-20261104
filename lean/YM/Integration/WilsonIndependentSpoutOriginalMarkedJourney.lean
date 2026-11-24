import YM.Integration.WilsonIndependentSpoutHaarHistory
import YM.Integration.WilsonIndependentSpoutMarkJourney

/-! A physical paid Haar chart reads the same complete marked report as the canonical chart from every actual birth date. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOriginalMarkedJourney
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Atlas RegulatorIR.Epoch Precision
open WilsonIndependentSpoutFundedClocks (clock)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Oracle.Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)
    (A:W→Levels G)(s:W→ℕ)(p:ℕ)

def source (O:ChartRatio G)(v:Page M)(X:Era G ℝ):RegulatorIR.Diagram.Orders (Foot G):=
  WilsonIndependentConditionalCoordinateHeat.orders (WilsonIndependentConditionalNativeLinks.coarse G) (mix (clock A O s v) X.2)

theorem entry (O:ChartRatio G)(valid:LocalRatio O)(v:Page M)(X:Era G ℝ):
    source A s O v X=WilsonIndependentNotebookPayrollMark.source A s v X:=by
  unfold source WilsonIndependentNotebookPayrollMark.source clock
  rw [WilsonIndependentSpoutHaarHistory.clock valid (XSpace.Bare.chart_ratio G)]

theorem original (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z D A s p f)
    (simple:G.Simple)(O:ChartRatio G)(valid:LocalRatio O)(k:ℕ)(bill:(C.payroll Y G Z (sheet D)).Report k)
    (w:W)(b:ℕ)(hb:b≤M w)(X:Era G ℝ)(auth:Auth k X)
    (birth:RegulatorIR.Clocks.Matches p (bill.main ⟨w,b,hb⟩) (source A s O ⟨w,b,hb⟩ X))
    (j:ℕ)(hj:b≤j)(fit:j≤M w):
    RegulatorIR.Clocks.Matches p (bill.main ⟨w,j,fit⟩)
      (source A s O ⟨w,j,fit⟩ (cruises (A w) O (s w+M w) k (s w+(M w-b)) (s w+(M w-j)) X)):=by
  rw [entry A s O valid] at birth ⊢
  rw [WilsonIndependentSpoutHaarHistory.original valid (XSpace.Bare.chart_ratio G)]
  exact WilsonIndependentSpoutMarkJourney.original C Y Z D A s p read simple k bill w b hb X auth birth j hj fit

end YM.Integration.WilsonIndependentSpoutOriginalMarkedJourney
