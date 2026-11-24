import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.IsolatedZeros
import YM.MS.Shine.Heart

set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Flux Landau Arts Arc Wire Rock
open scoped Topology ContDiff
variable {G:Gauge} {F H:Mob G} {f:ℂ→ Mob G} {n:ℕ}
def Pick (n:ℕ)(f:ℂ→Mob G)(F:Mob G): Prop:=
   match n with
   | 0=> Lift f F
   | n+1=> ∃ H:Mob G,Lift f H∧Pick n (slip f H) F
lemma given (h:Live f): ∀ n:ℕ,∃ F:Mob G,Pick n f F:= by
   intro n; induction n generalizing f with| zero=> exact h| succ n ih=> obtain ⟨F,h⟩:=h; obtain ⟨H,hx⟩:= ih (Lift.hols h); exact ⟨H,F,h,hx⟩
end YM.MS.Shine
