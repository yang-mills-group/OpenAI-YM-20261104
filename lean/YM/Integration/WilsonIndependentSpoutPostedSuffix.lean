import YM.Integration.WilsonIndependentSpoutHaarHistory
import YM.Integration.WilsonIndependentSpoutOriginalMarkedJourney

/-! A physical paid Haar chart reads the same complete marked report as the canonical chart from every actual birth date. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPostedSuffix
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Atlas RegulatorIR.Epoch Precision
open WilsonIndependentSpoutFundedClocks (clock)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Oracle.Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)
    (A:W→Levels G)(s:W→ℕ)(p:ℕ)

open WilsonIndependentSpoutOriginalMarkedJourney (source)
open RegulatorIR.Diagram

/-- Start a new mark at the selected age of this existing unmarked run. -/
def post (k:ℕ)(w:W)(b:ℕ)(X:Orders (Foot G)) : (l:ℕ) → b+l≤M w → Orders (Foot G)
  | 0, _ => X
  | l+1, h =>
    let f:Flap M:=⟨w,b+l,by omega⟩
    (C.devices Y G Z (sheet D) f).each k ((C.payroll Y G Z (sheet D)).bulk f.prev)
      (post k w b X l (by omega))

theorem original (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z D A s p f)
    (simple:G.Simple)(O:ChartRatio G)(valid:LocalRatio O)(k:ℕ)(w:W)(b:ℕ)(hb:b≤M w)
    (X:Era G ℝ)(auth:Auth k X)(l:ℕ)(fit:b+l≤M w):
    RegulatorIR.Clocks.Matches p
      (post C Y Z D k w b (source A s O ⟨w,b,hb⟩ X) l fit)
      (source A s O ⟨w,b+l,fit⟩ (cruises (A w) O (s w+M w) k (s w+(M w-b)) (s w+(M w-(b+l))) X)):=by
  simp_rw [WilsonIndependentSpoutOriginalMarkedJourney.entry A s O valid,
    WilsonIndependentSpoutHaarHistory.original valid (XSpace.Bare.chart_ratio G)]
  induction l with
  | zero =>
    simp only [post,Nat.add_zero,cruises_top]
    exact fun _ _=>rfl
  | succ l ih =>
    let f:Flap M:=⟨w,b+l,by omega⟩
    let c:=s w+(M w-b)
    let m:=s w+(M w-(b+(l+1)))
    let N:=s w+M w
    have step:m+1=s w+(M w-(b+l)):=by dsimp only [m];omega
    have between:m<c:=by dsimp only [m,c];omega
    let U:=cruises (A w) (XSpace.Bare.chart G) N k c (s w+(M w-(b+l))) X
    have legit:Auth k U:=cruising (A w) simple (XSpace.Bare.chart_ratio G)
      (by dsimp only [c];omega) (by dsimp only [c,N];omega) auth
    let F:=C.devices Y G Z (sheet D) f
    have reflGrid:GridM F F p:=⟨rfl,rfl,fun _ _=>rfl⟩
    have moving:=reflGrid.wave_step (m:=k) (T:=(C.payroll Y G Z (sheet D)).bulk f.prev)
      (fun _ _=>rfl) (ih (by omega))
    have issue:=read f k U legit
    rw [show s w+(M w-(b+(l+1)))=m from rfl, cruises_sub (A w) (XSpace.Bare.chart G) N k X between,step]
    exact fun e he=>(moving e he).trans (issue e he)

end YM.Integration.WilsonIndependentSpoutPostedSuffix
