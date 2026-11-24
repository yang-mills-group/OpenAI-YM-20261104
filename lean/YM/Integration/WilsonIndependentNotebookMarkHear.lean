import YM.Integration.WilsonIndependentPostedInlet
import YM.Integration.WilsonIndependentPostedMark
import YM.Integration.WilsonIndependentConditionalNativeVerse
import YM.Integration.WilsonIndependentConditionalFiniteGrant
import YM.Integration.WilsonIndependentSpoutFiniteExitRows

/-! The full normalized marked heat, on every true finite bare torus and on
the corresponding elected notebook, before restoring an external weight. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookMarkHear
open Function Matrix Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Halo
open RegulatorIR.Ledger RegulatorIR.Calibration WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalNativeLinks (joint coarse)
open WilsonIndependentConditionalUnshiftedQuiet (kernel matrix)
open WilsonIndependentConditionalUnshiftedExit (post ends)
open WilsonIndependentConditionalRawSpout (finite)
open WilsonIndependentPostedInlet (incoming quiet)
open WilsonIndependentConditionalCoordinateHeat (orders ranks)
open RegulatorIR.Diagram
open scoped Classical BigOperators Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
variable (C:Circuit M ss)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(A:Levels G)(s:ℕ)

def output (k:ℕ)(X:Era G ℝ)(n:Side):Pal ℝ (Woods G n):=
  let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let P:=loose A m
  let S:=mStep A n m;let F:=repeatF S;let H:=freeForms A N (m+1)
  let Ñ:=XSpace.Bare.chart G;let b:=n*P.L;let V:=(story A Ñ N (m+1)).1 b
  let α:=tale (D f.prev).dine;let T:=WilsonIndependentSpoutUnshiftedPost.bank P n (C.bore G Z (sheet D) f) α V
  let U:=panSlice G S F (extractV G S F (roam A N m n))
  WilsonIndependentSpoutFiniteExitRows.pulled U (finite (fillSlots (Woods G n) (FreeResolvent.covariance G S F H)) T
    (srCold (mix α (X.1 b)) 0) k)

theorem original (Y:Program K)(R:WilsonIndependentPublicFreeTrain.Matches A C K s f.volW)
    (simple:G.Simple)(k:ℕ)(X:Era G ℝ)(auth:Auth k X)(d e r:ℕ)(he:e≤d):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let Ñ:=XSpace.Bare.chart G
    let α:=tale (D f.prev).dine
    Bends 0 (fun n=>output C Z D f A s k X n e r)
       (WilsonIndependentConditionalCoordinateHeat.row (coarse G).symm
         ((C.devices Y G Z (sheet D) f).each k (WilsonIndependentSpoutReportedQuiet.port A Ñ N (m+1) α)
           (orders (coarse G) (mix α X.2)) e r)):=by
  intro N m Ñ α
  let B:=loose A m;let H:=freeForms A N (m+1)
  let U:=incoming C Z D f A Ñ N (m+1) α B
  let Q:=quiet C Y Z D f A Ñ N (m+1) α B
  let S:=WilsonIndependentConditionalUnshiftedMark.word B (fun n=>mix α (X.1 n))
  let Mv:=slidesJ B 0 (mix α X.2)
  let Γ:=kernel B (shuttleM (conditional A N m));let E:=post B (shuttleM (feedA A N m))
  have young:m<N:=by dsimp [N,m];have:=f.ok;omega
  have patch:B=C.pactP f:=R.patches f rfl
  let ratio:=XSpace.Bare.chart_ratio G
  have reach:=WilsonIndependentPostedInlet.earned C Y Z D f A Ñ N (m+1) α B patch simple ratio young
  have sym:=WilsonIndependentPostedInlet.pure C Z D f A Ñ N (m+1) α B patch simple ratio young
  have test:=WilsonIndependentConditionalFiniteGrant.original A (N:=N) young (V:=U) (P:=Q) (F:=S) (Z:=Mv)
    (fun i _ u h=>reach i u h) (fun n i _=>sym n i)
    (fun i _ j=>WilsonIndependentPostedMark.earned B X auth α i j)
    (fun n i _=>WilsonIndependentPostedMark.pure B X auth α n i) k e r he
  let roof:=scoop (Packet.draft E.transpose (endHeat k Γ (logHeat Γ Q false) Mv e r))
  have paid:Bends 0 (fun n=>output C Z D f A s k X n e r) roof:=by
    convert test using 1
    funext n q
    have proj:=WilsonIndependentPostedMark.original B A.clock.kernel H (roam A N m) n
      (WilsonIndependentSpoutUnshiftedPost.bank B n (C.bore G Z (sheet D) f) α ((story A Ñ N (m+1)).1 (n*B.L)))
      (srCold (mix α (X.1 (n*B.L))) 0) k e r q
    simp only [output,WilsonIndependentSpoutFiniteExitRows.pulled,fade_plug,U,S,Ñ,N,m,α,B,H,mStep,mer,teller,xree]
      at proj ⊢
    convert proj using 1
    congr 3
  have prior:=WilsonIndependentPostedInlet.head C Y Z D f A Ñ N (m+1) α B
  have named:=WilsonIndependentConditionalNativeVerse.submitted R Y Z (sheet D) f rfl
    (WilsonIndependentSpoutReportedQuiet.port A Ñ N (m+1) α) (orders (coarse G) (mix α X.2)) Q (mix α X.2)
    (fun i _ u _=>prior i u) (fun _ _=>rfl) k he r
  change _=WilsonIndependentConditionalCoordinateHeat.row (coarse G) roof at named
  rw [named]
  convert paid using 1
  funext q
  change roof (coarse G∘(coarse G).symm∘q)=roof q
  congr 1;funext i;exact (coarse G).apply_symm_apply _

end YM.Integration.WilsonIndependentNotebookMarkHear
