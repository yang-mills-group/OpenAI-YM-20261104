import YM.Integration.WilsonIndependentNotebookCubicSeeds
import YM.Integration.WilsonIndependentSpoutMarkJourney

/-! The difference of the two published ordinary reports on one elected
notebook equals the four genuinely propagated cubic deposits and its
disconnected remainder, on every held axis through the issued order. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
namespace YM.Integration.WilsonIndependentNotebookCubicReports
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Oracle RegulatorIR.Prim
open WilsonIndependentNotebookPayrollMark (source)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
variable (C:RegulatorIR.Oracle.Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)
variable (A:W→Levels G)(s:W→ℕ)(p:ℕ)

/-- Both measured inlets use the same AB and the two openly declared third
fields on the same fine page. Earlier vacuum history may extend above it. -/
theorem original (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z D A s p f)
    (simple:G.Simple){i j k:ℕ}(actual fitted:(C.payroll Y G Z (sheet D)).Report (i+j+k))
    (w:W)(birth n:ℕ)(fit:birth+n ≤ M w){X B U V:Era G ℝ}
    (x:Auth i X)(b:Auth j B)(u:Auth k U)(v:Auth k V)
    (observed:Matches p (actual.main ⟨w,birth,by omega⟩)
      (source A s (⟨w,birth,by omega⟩:Page M) (agateV (agateV X B) U)))
    (matched:Matches p (fitted.main ⟨w,birth,by omega⟩)
      (source A s (⟨w,birth,by omega⟩:Page M) (agateV (agateV X B) V))):
    let stop:Page M:=⟨w,birth+n,fit⟩;let m:=s w+(M w-(birth+n));let N:=s w+M w
    Matches p (actual.main stop-fitted.main stop) (source A s stop
      (WilsonIndependentNotebookCubicSeeds.bill (A w) (XSpace.Bare.chart G) m N i j k n X B U V)):=by
  intro stop m N
  let Ñ:=XSpace.Bare.chart G
  let raw:=agateV (agateV X B) U;let pay:=agateV (agateV X B) V
  let J:=cruises (V:=ℝ) (A w) Ñ N (i+j+k) (m+n) m
  have height:m+n=s w+(M w-birth):=by dsimp [m];omega
  have span:m+n ≤ N:=by dsimp [m,N];omega
  have honest:Matches p (actual.main stop) (source A s stop (J raw)):=by
    dsimp only [J];rw [height]
    exact WilsonIndependentSpoutMarkJourney.original C Y Z D A s p read simple (i+j+k) actual
      w birth (by omega) raw ((x.manor b).manor u) observed (birth+n) (by omega) fit
  have proposed:Matches p (fitted.main stop) (source A s stop (J pay)):=by
    dsimp only [J];rw [height]
    exact WilsonIndependentSpoutMarkJourney.original C Y Z D A s p read simple (i+j+k) fitted
      w birth (by omega) pay ((x.manor b).manor v) matched (birth+n) (by omega) fit
  have signed:J raw-J pay=WilsonIndependentNotebookCubicSeeds.bill (A w) Ñ m N i j k n X B U V:=
    WilsonIndependentNotebookCubicSeeds.original (A w) simple (XSpace.Bare.chart_ratio G) span x b u v
  rw [←signed,WilsonIndependentNotebookOrdinaryProduct.subtract]
  intro e he
  exact congrArg₂ (·-·) (honest e he) (proposed e he)

end YM.Integration.WilsonIndependentNotebookCubicReports
