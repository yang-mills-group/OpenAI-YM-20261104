import YM.Integration.WilsonIndependentSpoutEnrolledRosterExit
import YM.Integration.WilsonIndependentReportedRosterStops

/-! Every earlier enrolled raw source, on its own original chart and at any stopping page. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalEnrolledMerStop
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Atlas RegulatorIR.Epoch Precision
open RegulatorIR.Profiles RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Halo RegulatorIR.Cluster
open WilsonIndependentRawRosterWord (degree bank)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentSpoutOriginalMarkedJourney (source)
open WilsonIndependentPublicReportComplex (apply)
open scoped Classical
variable {G:Gauge}{I J:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    {M:J→ℕ}{sides:Page M → Side}{K:KernelChoices}
    (C:Oracle.Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(F:Tent M)
    (A:J→Levels G)(s:J→ℕ)(O:ChartRatio G)
    (σ:I→Bool)(d:I→ℕ)(key:∀i,(R.family.labels.level (d i)).Index){E:I→ℕ}(cut:∀i,d i<E i)
    (arms:Composite I)(sites:J → I → Cover)
local notation "rank₀" => arms.accounts (degree R d key)
local notation "paid" => WilsonIndependentRawRosterOrbit.report R W σ d key arms (C.payroll Y G Z (sheet F)) sites
local notation "b₀" w:max => field R W σ d key cut (sites w) arms

def aged (stop:Choice M)(w:J):RegulatorIR.Diagram.Orders (Foot G):=
  source A s O (stop.choose w) (cruises (A w) O (s w+M w) rank₀ (s w+M w) (s w+(M w-stop.age w)) (b₀ w))

theorem original (simple:G.Simple)(valid:LocalRatio O)(p:ℕ)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z F A s p f)(stop:Choice M)(w:J):
    RegulatorIR.Clocks.Matches p ((paid).main (stop.choose w))
      (aged R W A s O σ d key cut arms sites stop w):=by
  obtain ⟨auth,_⟩:=WilsonIndependentMatchedOpeningComplete.original R W σ d key cut arms (sites w) (L:=M) A s w
  have first:RegulatorIR.Clocks.Matches p ((paid).main (Page.opening M w))
      (source A s O (Page.opening M w) (b₀ w)):=by
    rw [WilsonIndependentSpoutOriginalMarkedJourney.entry A s O valid]
    exact WilsonIndependentMatchedOpeningComplete.measured R W σ d key cut arms (sites w) A s w p
  have later:=WilsonIndependentSpoutOriginalMarkedJourney.original C Y Z F A s p read simple O valid rank₀ paid
    w 0 (Nat.zero_le _) (b₀ w) auth first (stop.age w) (Nat.zero_le _) (stop.young w)
  simpa only [aged,Choice.choose,Nat.sub_zero] using later

def series (X:RegulatorIR.Diagram.Orders (Foot G)):PowerSeries ℂ:=
  PowerSeries.mk fun j=>(note (X j 0):ℂ)

theorem reported (simple:G.Simple)(valid:LocalRatio O)(p:ℕ)
    (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z F A s p f)(stop:Choice M)(w:J)
    (scale:Feeds)(roof q:ℕ)(hq:q≤p):
    PowerSeries.coeff q (apply scale roof (series ((paid).main (stop.choose w)))) =
    PowerSeries.coeff q (apply scale roof (series (aged R W A s O σ d key cut arms sites stop w))):=by
  have sound:=original R W C Y Z F A s O σ d key cut arms sites simple valid p read stop w
  rw [WilsonIndependentPublicReportComplex.coefficients,WilsonIndependentPublicReportComplex.coefficients]
  apply Finset.sum_congr rfl
  intro i hi
  have ip:=Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hq
  simp only [series,PowerSeries.coeff_mk,sound i ip]

end YM.Integration.WilsonOriginalPublicNodalEnrolledMerStop
end
