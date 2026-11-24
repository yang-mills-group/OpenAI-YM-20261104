import YM.Integration.WilsonIndependentSpoutPayrollRoute
import YM.Integration.WilsonIndependentNotebookVacuumEdge

/-! The real bare prescription is the normalized Mer vacuum on every page of the elected course. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutEarnedNotebook
open Function Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Power WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Clocks.Warp RegulatorIR.Pupil RegulatorIR.Ward RegulatorIR.Budget
open PertExtension Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutFundedClocks (age clock)
open WilsonIndependentSpoutPayrollRoute (reported Edges)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(A:W→Levels G)(s:W→ℕ)

theorem original (simple:G.Simple)(inc:∀w,WilsonIndependentPublicFreeTrain.Matches (A w) C K (s w) w)(p:ℕ):
    let Ñ:=XSpace.Bare.chart G
    ∃D:Tent M,(∀c:G.ColorIndex,Notebook C Y G Z c (RegulatorIR.FVAAlt2.Rocket.native M) D p) ∧
        (∀v,RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk v) (reported A s v)) ∧
        (∀v,Squares p (tale (D v).dine) (clock A Ñ s v) ∧
         Squares p (tale (sheet D v).beta) (((clock A Ñ s v)⁻¹)^2)) ∧
        ∀ (f:Flap M) (n:Side),WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f
          (A f.volW) (s f.volW) p n:=by
  intro Ñ
  obtain ⟨D,start,cash,heard⟩:=WilsonIndependentSpoutMeasuredCourse.original C Y Z A s simple inc p
  have edge:Edges C Y Z D A s p:=by
    intro f;dsimp only;intro e _ he r hr
    exact WilsonIndependentNotebookVacuumEdge.original Y Z D f (inc _) simple p (heard f) e he r hr
  have allPages:=WilsonIndependentSpoutPayrollRoute.route C Y Z D A s simple p start (fun v=>(cash v).1) edge
  refine ⟨D,fun c=>⟨?_,start⟩,allPages,fun v=>⟨(cash v).1,(cash v).2.1⟩,heard⟩
  intro v
  refine ⟨?_,(cash v).2.2.1⟩
  intro e he pos
  rw [allPages v e he]
  have token:= (cash v).2.2.2 e he c
  exact (show reported A s v e 2=WilsonIndependentSpoutKineticToken.direct
    (mix (clock A Ñ s v) (actionW (A v.bindW) Ñ (s v.bindW+M v.bindW) (age s v)) e 2) from by
      ext1 q;simp only [reported,WilsonIndependentSpoutReportedQuiet.port,WilsonIndependentSpoutReportedQuiet.cover,
        if_neg (Nat.ne_of_gt pos),Pi.neg_apply,WilsonIndependentSpoutKineticToken.direct,actionW];rfl) ▸ token

end YM.Integration.WilsonIndependentSpoutEarnedNotebook
