import YM.Integration.WilsonPhysicalExteriorFiniteLog
import YM.Integration.WilsonPhysicalExteriorResolvedReadout

/-! Uniform log degree on the exact finite original normalized Wilson
coefficient, over every side, physical location and branch in a trial.
The inner episode here is the original finite Wilson stationary moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorNativeLog
open Function Finset Lattice Labels Source Precision
open MS MS.Land MS.Dial MS.Menus MS.Rake MS.Wind MS.Lifting MS.Logarithm
open RegulatorIR RegulatorIR.FVAAlt2 YM.FVAAlt2 MS.Orbit
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation
open scoped Topology BigOperators Classical

variable {G:Gauge} {Λ:Frames G} {H:Hol G} {X W:Type} [LinearOrder W] [Fintype W]
variable (D:ChartRatio G) (R:Lobby.Registry Λ H)
variable {B:MS.Local.Physical.Deck G} (Q:Prescription B) (p:W→Label B)

def episode {n:Side} (x:W→Site n) : Sound.Formal.Episode W Λ :=
  fun d v => Lobby.ΦbaseT D univ (fun i j=>((Λ.level (d i)).grades j).2)
    (fun i j=>fieldAt (R.use (d i)) j (x i)) v

theorem original {n:Side} (x:W→Site n) (u:ℝ) {ε:ℝ} (hε:ε≠0) :
    Lobby.newEra D R Q u p x ε=Sound.Formal.dated Q u R p ε (episode D R x) := by
  rw [Lobby.tot_cost D R Q u p x ε hε]
  rfl

theorem finite (T:Trial X W) (k:ℕ) :
    Ready (fun u i=>Lobby.evaluateR D R Q p T u k i) := by
  have good:=WilsonPhysicalExteriorFiniteLog.dated Q R p T.profile.θ (Lobby.spacing T)
    (fun i=>episode D R (Lobby.situated T i)) k
  convert good using 1
  funext u i
  exact congrArg (PowerSeries.coeff k) (original D R Q p (Lobby.situated T i) (u-T.profile.θ i)
    (Real.exp_ne_zero _))

end YM.Integration.WilsonPhysicalExteriorNativeLog
end
