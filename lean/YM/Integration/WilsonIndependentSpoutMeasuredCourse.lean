import YM.Integration.WilsonIndependentSpoutMeasuredHearing

/-! One honest clock before all finite boards and later marked bids. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMeasuredCourse
open Matrix PowerSeries Function Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Oracle
open RegulatorIR.Calibration RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Prim
open RegulatorIR.Pupil RegulatorIR.Ward WilsonIndependentPublicFreeTrain WilsonIndependentSpoutFundedClocks
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(A:W→Levels G)(s:W→ℕ)

include Y in
theorem original (simple:G.Simple)(inc:∀w,Matches (A w) C K (s w) w)(p:ℕ):
    let Ñ:=XSpace.Bare.chart G
    ∃D:Tent M,(∀w,D (Page.opening M w)=Calibration.dawn)∧
      (∀v,Squares p (tale (D v).dine) (clock A Ñ s v)∧
        Squares p (tale (sheet D v).beta) (((clock A Ñ s v)⁻¹)^2)∧Seconds (sheet D v) p∧
        ∀e≤p,∀c:G.ColorIndex,Rules.token (WilsonIndependentSpoutKineticToken.direct (mix (clock A Ñ s v)
          (actionW (A v.bindW) Ñ (s v.bindW+M v.bindW) (age s v)) e 2)) c=biases (sheet D v) e)∧
      ∀(f:Flap M)(n:Side),WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f (A f.volW) (s f.volW) p n:=by
  intro Ñ
  obtain ⟨D,start,book⟩:=WilsonIndependentSpoutFundedClocks.original A Ñ s simple (XSpace.Bare.chart_ratio G) p
  refine ⟨D,start,book,?_⟩
  intro f n
  apply WilsonIndependentSpoutMeasuredHearing.given C Y Z D f (A f.volW) (s f.volW) (inc _) simple p _ n
  have depth:=f.ok
  let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1))
  have date:N-(m+1)=f.offset:=by dsimp only [N,m];omega
  have older:age s f.prev=m+1:=by change s f.volW+(M f.volW-f.offset)=s f.volW+(M f.volW-(f.offset+1))+1;omega
  change Squares p (tale (D f.prev).dine) (relativeC (A f.volW) Ñ N (m+1) (N-(m+1)))
  rw [date,←older]
  exact (book f.prev).1

end YM.Integration.WilsonIndependentSpoutMeasuredCourse
