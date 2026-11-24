import YM.Integration.WilsonIndependentSpoutPayrollSeeds
import YM.Integration.WilsonIndependentSpoutMeasuredCourse
import YM.Integration.WilsonIndependentLicensedCircuit

/-! Induction along the elected finite history, using its own original bare page and clock. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPayrollRoute
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Power WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Clocks.Warp RegulatorIR.Halo RegulatorIR.Binding RegulatorIR.Pupil RegulatorIR.Ward
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open PertExtension Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutFundedClocks (age clock)
open WilsonIndependentSpoutReportedQuiet (port)
open scoped Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)
    (A:W→Levels G)(s:W→ℕ)

def reported (v:Page M):Orders (Foot G):=
  let Ñ:=XSpace.Bare.chart G;port (A v.bindW) Ñ (s v.bindW+M v.bindW) (age s v) (clock A Ñ s v)

def Edges (p:ℕ):Prop:=∀ f:Flap M,
    let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1))
    let Ñ:=XSpace.Bare.chart G;let T:=port (A f.volW) Ñ N (m+1) (tale (D f.prev).dine)
    let U:=port (A f.volW) Ñ N m (relativeC (A f.volW) Ñ N m (N-m))
    ∀ e,0<e→e≤p→∀r,0<r→(C.devices Y G Z (sheet D) f).pure T e r=U e r

theorem route (simple:G.Simple)(p:ℕ)(start:∀w,D (Page.opening M w)=Calibration.dawn)
    (cash:∀v,Squares p (tale (D v).dine) (clock A (XSpace.Bare.chart G) s v))
    (steps:Edges C Y Z D A s p):
    ∀v,RegulatorIR.Clocks.Matches p ((C.payroll Y G Z (sheet D)).bulk v) (reported A s v):=by
  let Ñ:=XSpace.Bare.chart G; let Q:=C.payroll Y G Z (sheet D)
  have unit (v:Page M):constantCoeff (clock A Ñ s v)=1:=by
    apply angularC simple (XSpace.Bare.chart_ratio G)
    have h:=v.good;unfold age;omega
  apply Page.proves
  · intro w
    have flat:sheet D (Page.opening M w)=Clocks.flat:=by
      change (D (Page.opening M w)).scale=_;rw [start];exact RegulatorIR.FVAAlt2.Rocket.still
    exact WilsonIndependentSpoutPayrollSeeds.initial C (sheet D) w flat (A w) Ñ simple
      (XSpace.Bare.chart_ratio G) (s w+M w) p
  intro f ih
  let N:=s f.volW+M f.volW;let m:=s f.volW+(M f.volW-(f.offset+1))
  let levels:=A f.volW; let F:=C.devices Y G Z (sheet D) f
  have hf:=f.ok
  have upper:age s f.prev=m+1:=by change s f.volW+(M f.volW-f.offset)=_;dsimp only [m];omega
  have clocked:RegulatorIR.Clocks.Matches p (Q.bulk f.prev)
      (port levels Ñ N (m+1) (tale (D f.prev).dine)):=by
    intro i hi
    have h:=WilsonIndependentSpoutPayrollSeeds.clock levels Ñ N (age s f.prev) (cash f.prev) (unit f.prev) i hi
    exact (ih i hi).trans (upper ▸ h.symm)
  have frozen:GridM F F p:=⟨rfl,rfl,fun _ _=>rfl⟩
  have downstream:=frozen.log_step clocked
  have lower:N-m=f.offset+1:=by dsimp only [N,m];omega
  intro e he
  by_cases zero:e=0
  · subst e
    exact (vacuum_lo _ (Q.cap_b (Halo.essential (C.lane Y G Z (sheet D))) f.next)).trans
      (WilsonIndependentSpoutPayrollSeeds.thermal ..).symm
  ext1 r
  by_cases empty:r=0
  · subst r
    rw [←Q.step_v]
    have h:=WilsonIndependentSpoutPayrollSeeds.scalar levels Ñ simple (XSpace.Bare.chart_ratio G) N m
      (by dsimp only [N,m];omega) (clock A Ñ s f.next) e
    exact h.symm
  calc
    Q.bulk f.next e r=F.pure (Q.bulk f.prev) e r:=by rw [←Q.step_v];rfl
    _=F.pure (port levels Ñ N (m+1) (tale (D f.prev).dine)) e r:=congr_fun (downstream e he) r
    _=port levels Ñ N m (relativeC levels Ñ N m (N-m)) e r:=steps f e (Nat.pos_of_ne_zero zero) he r (Nat.pos_of_ne_zero empty)
    _=reported A s f.next e r:=by rw [lower];rfl

end YM.Integration.WilsonIndependentSpoutPayrollRoute
