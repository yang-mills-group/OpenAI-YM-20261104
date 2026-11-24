import YM.Integration.WilsonIndependentSpoutFiniteExitRows

/-! The physical finite ordinates obtained by withdrawing the whole current
vacuum, together with their actual bulk limit at the next date. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutFiniteReportLaw
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Halo RegulatorIR.Diagram RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Pupil
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentSpoutUnshiftedPost (bank)
open WilsonIndependentSpoutFiniteExitRows (pulled)
open WilsonIndependentSpoutFundedClocks (age clock)
open PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Classical BigOperators Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(A:Levels G)(s:ℕ)

def output (n:Side):PChart G n:=
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let P:=loose A m
    let S:=mStep A n m;let F:=repeatF S;let H:=freeForms A N (m+1)
    let Ñ:=XSpace.Bare.chart G;let b:=n*P.L;let V:=(story A Ñ N (m+1)).1 b
    let α:=tale (D f.prev).dine;let T:=bank P n (C.bore G Z (sheet D) f) α V
    let U:=panSlice G S F (extractV G S F (roam A N m n))
    pulled U (WilsonIndependentConditionalRawVacuum.finite
      (fillSlots (Woods G n) (FreeResolvent.covariance G S F H)) T)

theorem measured (simple:G.Simple)(p:ℕ)(n:Side)
    (paid:WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f A s p n):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1))
    let α:=relativeC A (XSpace.Bare.chart G) N m (N-m)
    ∀e≤p,∀r,0<r→ output C Z D f A s n e r=WilsonIndependentSpoutReportedQuiet.finite A (XSpace.Bare.chart G) N m α e r n:=by
  intro N m α e hi r hr
  by_cases z:e=0
  · subst e
    unfold output WilsonIndependentSpoutFiniteExitRows.pulled WilsonIndependentConditionalRawVacuum.finite
    have initial (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))
        (α:Cost)(V:PChart G (n*P.L)):bank P n T α V 0=0:=by ext r q;rfl
    simp [abr_zero,initial,fade_zero,WilsonIndependentSpoutReportedQuiet.finite]
  simp only [WilsonIndependentSpoutReportedQuiet.finite,if_neg z]
  exact WilsonIndependentSpoutFiniteExitRows.original C Z D f A s simple p n paid e (Nat.pos_of_ne_zero z) hi r hr

theorem joined (simple:G.Simple)(p:ℕ)(paid:∀n,WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f A s p n):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1))
    let α:=relativeC A (XSpace.Bare.chart G) N m (N-m)
    ∀e≤p,∀r,0<r→Yields (fun n=>output C Z D f A s n e r)
       (WilsonIndependentSpoutReportedQuiet.cover A (XSpace.Bare.chart G) N m α e r):=by
  intro N m α e hi r hr
  have same:(fun n=>output C Z D f A s n e r)=WilsonIndependentSpoutReportedQuiet.finite A (XSpace.Bare.chart G) N m α e r:=
    funext fun n=>measured C Z D f A s simple p n (paid n) e hi r hr
  rw [same]
  exact WilsonIndependentSpoutReportedQuiet.earned A (XSpace.Bare.chart G) simple (XSpace.Bare.chart_ratio G) N m
    (by dsimp [N,m];omega) α e r

end YM.Integration.WilsonIndependentSpoutFiniteReportLaw
