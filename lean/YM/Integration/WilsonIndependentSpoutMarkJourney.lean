import YM.Integration.WilsonIndependentNotebookMarkedEdge

/-! An ordinary marked report propagates its whole registered word on the same inherited vacuum from its chosen page. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMarkJourney
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Atlas RegulatorIR.Epoch
open RegulatorIR.Clocks.Warp RegulatorIR.Halo RegulatorIR.Cluster
open WilsonIndependentNotebookPayrollMark (source)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:RegulatorIR.Oracle.Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)
    (A:W→Levels G)(s:W→ℕ)(p:ℕ)

theorem original (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z D A s p f)
    (simple:G.Simple)(k:ℕ)(bill:(C.payroll Y G Z (sheet D)).Report k)
    (w:W)(b:ℕ)(hb:b≤M w)(X:Era G ℝ)(auth:Auth k X)
    (birth:RegulatorIR.Clocks.Matches p (bill.main ⟨w,b,hb⟩) (source A s ⟨w,b,hb⟩ X))
    (j:ℕ)(hj:b≤j)(fit:j≤M w):
    RegulatorIR.Clocks.Matches p (bill.main ⟨w,j,fit⟩)
      (source A s ⟨w,j,fit⟩ (cruises (A w) (XSpace.Bare.chart G) (s w+M w) k
        (s w+(M w-b)) (s w+(M w-j)) X)):=by
  induction j,hj using Nat.le_induction with
  | base => simpa only [cruises_top] using birth
  | succ j hj ih =>
    let f:Flap M:=⟨w,j,fit⟩
    let c:=s w+(M w-b)
    let m:=s w+(M w-(j+1))
    let N:=s w+M w
    have step:m+1=s w+(M w-j):=by dsimp [m];omega
    have between:m<c:=by dsimp [m,c];omega
    let U:=cruises (A w) (XSpace.Bare.chart G) N k c (s w+(M w-j)) X
    have legit:Auth k U:=cruising (A w) simple (XSpace.Bare.chart_ratio G)
      (by dsimp [c];omega) (by dsimp [c,N];omega) auth
    have old:RegulatorIR.Clocks.Matches p (bill.main f.prev) (source A s f.prev U):=ih (by omega)
    let F:=C.devices Y G Z (sheet D) f
    have reflGrid:GridM F F p:=⟨rfl,rfl,fun _ _=>rfl⟩
    have moving:=reflGrid.wave_step (m:=k) (T:=(C.payroll Y G Z (sheet D)).bulk f.prev)
      (fun _ _=>rfl) old
    have issue:=read f k U legit
    change RegulatorIR.Clocks.Matches p (bill.main f.next)
      (source A s f.next (cruises (A w) (XSpace.Bare.chart G) N k c m X))
    rw [cruises_sub (A w) (XSpace.Bare.chart G) N k X between,step,←bill.step_m f]
    exact fun e he=>(moving e he).trans (issue e he)

end YM.Integration.WilsonIndependentSpoutMarkJourney
