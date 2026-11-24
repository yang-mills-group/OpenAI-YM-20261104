import YM.MS.Plum.Fence
/-!
# Vital commutation identities in D, without temporary compact momentum regulators

Public for Master and Sym calculus. Only z variable (still horizon normalized) with ∆ sign.
 No prepared gauge properties through correspondence. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plum
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans
open Momentum Metric
open scoped Topology ContDiff
variable {I J E F:Type}
 {G:Gauge}{U V W: Rip G}{m n:ℕ}{K: Shade G}{b c:Bool}{F H: Mob G}{x:ℂ}
lemma ink (h:closedF U c)(x:ℝ): closedF (twine x U) c:= fun i a b q hh=> h i a b q (right_ne_zero_of_mul hh)
lemma move_f (h:reverseF U)(x:ℝ): reverseF (twine x U) := by intro m i j p; unfold twine; rw [smul_neg,fruit_even,h m i j p]; ring
lemma tideZ (q: Shade G) (hx:∀ n,(q n).change (U n)=V n)(x:ℝ): ∀ n,(q n).change (twine x U n)=twine x V n:= by
   intro n; funext p q' i; simp only [Charge.change,twine,← hx]; simp only [mul_add,Finset.mul_sum]; congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
lemma rockGone {X:ℕ→Mob G}(hp:Drift b X F)(ht:Drift b X H): F=H:=funext fun i=> funext fun l=> tendsto_nhds_unique (hp.now i l) (ht.now i l)
variable (Hf:Form0 b F)(HU:Knot b U)(hu:closedF U false)
include Hf HU hu
lemma qft (he:x∈Town)(hq: Priced K)(hK:CountsD b K)(H:Knot b V)(hz: ∀ m,(K m).change (U m)=V m) : portZ K (ocean x U F)+ ocean x V F=ocean x U (portZ K F) := by
   let P:= oceansLine (steak Hf) (newer HU) he; obtain heq:= P.portQ hK hq;
   apply rockGone (heq.add (oceansLine (steak Hf) (newer H) he)); convert! oceansLine (Drift.portQ (steak Hf) hK hq) (newer HU) he using 1; funext i; exact capA Hf (tried HU _ (being i) (sold i)) (ink hu _) hq hK (tried H _ (being i) (sold i)) (tideZ K hz _) x he -- variable From x.. sign

variable (HV: Knot b V)(hv:closedF V true)
include HV hv
lemma lampLamp (h:Rock.sym F)(he:x∈Town): ocean x V (ocean x U F)=ocean x U (ocean x V F) := by
   let X := steak Hf; apply rockGone (oceansLine (oceansLine X (newer HU) he) (newer HV) he); convert oceansLine (oceansLine X (newer HV) he) (newer HU) he using 1; funext n; exact capD Hf (tried HU (fade n) (being n) (sold n)) (ink hu _) (tried HV _ (being n) (sold n)) (ink hv _) h x he
lemma flightD (Hh:Form0 b H)(hf:Rock.sym F) (hp:tide F)(hh: Rock.sym H)(he:x∈Town)(hx:reverseF U)(hY:reverseF V) : ocean x V (arbor U F H)+arbor V (ocean x U F) H+arbor V F (ocean x U H)=ocean x U (arbor V F H)+arbor U (ocean x V F) H+arbor U F (ocean x V H) := by
   let X:= steak Hf; let Y:= steak Hh; let R:=newer HU; let S:=newer HV; have hA i:= ink hu (fade i); have hB i:= ink hv (fade i); have hC i:= move_f hx (fade i); have hD i:= move_f hY (fade i)
   apply rockGone (((oceansLine (arborial X R Y hu hA hx hC) S he).add (arborial (oceansLine X R he) S Y hv hB hY hD)).add (arborial X S ( oceansLine Y R he) hv hB hY hD))
   convert ((oceansLine (arborial X S Y hv hB hY hD) R he).add (arborial (oceansLine X S he) R Y hu hA hx hC)).add (arborial X R (oceansLine Y S he) hu hA hx hC) using 1; funext i; exact capT Hf (tried HU _ (being i) (sold i)) (hA i) (tried HV _ (being i) (sold i)) (hB i) hf x he Hh hh hp (hC i) (hD i)
end YM.MS.Plum
