import YM.MS.Rock.Claim
import YM.MS.Rock.Wing
import YM.MS.Shine.Ash

set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Flux Landau Arts Arc Wire Rock
open scoped Topology ContDiff
variable {G:Gauge} {R T:ℝ} {c:ℂ} {f:ℂ→ Mob G}
abbrev disc (R:ℝ):= ball (0:ℂ) R
def Golden (f:ℂ→ Mob G)(z:ℂ): Mob G:= fun a l=> dslope (fun z=> f z a l) 0 z
lemma hung (h: c≠0): Golden f c=c⁻¹ • ( f c-f 0):= by
  funext m l
  rw [Golden, dslope_of_ne _ h, slope]
  simp
lemma HolG (h:Hol (disc R) f)(hr:0<R): Hol (disc R) (Golden f):= by
    have he {m E} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (w:Touch G m E): Plots (disc R) (fun i=> fieldVal ( Golden f i m) w):= rebot hr ⟨fun c R hc hp=> h.price c R hc hp m E w,fun _=> h.top m _⟩
    exact ⟨fun c T ht hp m E _ _ _ w=> (he w).span c T ht hp, fun _ l=> by simpa only [fieldVal,ray_sail] using (he (ray l)).root (1:ℝ)⟩ -- ray_sail rfl? probe.
end YM.MS.Shine
