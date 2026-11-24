import YM.Integration.WilsonIndependentConditionalNativeVacuum
import YM.Integration.WilsonIndependentConditionalPureReceiver
import YM.Integration.WilsonIndependentPostedInlet
import YM.Integration.WilsonIndependentPostedProjection
import YM.Integration.WilsonIndependentSpoutFiniteReportLaw

/-! On the selected inversion circuit the true finite Wilson vacuum, after a
single normalized step, gives every nonconstant row of the native notebook. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookVacuumEdge
open Function Matrix Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Halo
open RegulatorIR.Ledger RegulatorIR.Calibration WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalNativeLinks (joint coarse)
open WilsonIndependentConditionalUnshiftedQuiet (kernel matrix)
open WilsonIndependentConditionalUnshiftedExit (post ends)
open WilsonIndependentConditionalRawVacuum (finite)
open WilsonIndependentPostedInlet (incoming quiet)
open RegulatorIR.Diagram
open scoped Classical BigOperators Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
variable {A:Levels G}{C:Circuit M ss}{s:ℕ}
theorem original (Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (R:WilsonIndependentPublicFreeTrain.Matches A C K s f.volW)(simple:G.Simple)(p:ℕ)
    (paid:∀n,WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f A s p n):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let Ñ:=XSpace.Bare.chart G
    let α:=tale (D f.prev).dine;let β:=relativeC A Ñ N m (N-m)
    ∀e≤p,∀r,0<r→(C.devices Y G Z (sheet D) f).pure
        (WilsonIndependentSpoutReportedQuiet.port A Ñ N (m+1) α) e r=
        WilsonIndependentSpoutReportedQuiet.port A Ñ N m β e r:=by
  intro N m Ñ α β e he r hr
  let B:=loose A m;let H:=freeForms A N (m+1)
  let U:=incoming C Z D f A Ñ N (m+1) α B
  let Q:=quiet C Y Z D f A Ñ N (m+1) α B
  let Γ:=kernel B (shuttleM (conditional A N m));let E:=post B (shuttleM (feedA A N m))
  have young:m<N:=by dsimp [N,m];have:=f.ok;omega
  have patch:B=C.pactP f:=R.patches f rfl
  let ratio:=XSpace.Bare.chart_ratio G
  have reach:=WilsonIndependentPostedInlet.earned C Y Z D f A Ñ N (m+1) α B patch simple ratio young
  have sym:=WilsonIndependentPostedInlet.pure C Z D f A Ñ N (m+1) α B patch simple ratio young
  have income:=WilsonIndependentConditionalPureReceiver.original A (N:=N) (d:=p) young (V:=U) (T:=Q)
    (fun i _ u h=>reach i u h) sym e r he hr
  let roof:=scoop (Packet.draft E.transpose (ceaseHeat Γ Q false e r))
  have check:Yields (fun n=>WilsonIndependentSpoutFiniteReportLaw.output C Z D f A s n e r) roof:=by
    convert income using 1
    funext n q
    have projection:=WilsonIndependentPostedProjection.original B A.clock.kernel H (roam A N m) n
      (WilsonIndependentSpoutUnshiftedPost.bank B n (C.bore G Z (sheet D) f) α
        ((story A Ñ N (m+1)).1 (n*B.L))) e r q
    simp only [WilsonIndependentSpoutFiniteReportLaw.output,WilsonIndependentSpoutFiniteExitRows.pulled,fade_plug,U,Ñ,N,m,α,B,H,mStep,mer,teller,xree] at projection ⊢
    convert projection using 1
    congr 3
  have equal:=check.unique (WilsonIndependentSpoutFiniteReportLaw.joined C Z D f A s simple p paid e he r hr)
  have before:=WilsonIndependentPostedInlet.head C Y Z D f A Ñ N (m+1) α B
  have native:=WilsonIndependentConditionalNativeVacuum.submitted R Y Z (sheet D) f rfl
    (WilsonIndependentSpoutReportedQuiet.port A Ñ N (m+1) α) Q (fun i _ j _=>before i j) he hr
  change _=WilsonIndependentConditionalCoordinateHeat.row (coarse G) roof at native
  rw [native,equal];rfl

end YM.Integration.WilsonIndependentNotebookVacuumEdge
