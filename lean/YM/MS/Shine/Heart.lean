import YM.MS.Shine.Later
import YM.MS.Shine.Perch

set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Flux Landau Arts Arc Wire Rock
open scoped Topology ContDiff
variable {G:Gauge} {R:ℝ} {F H:Mob G} {x:ℂ→ℂ} {f g:ℂ→ Mob G}
abbrev Lift (f:ℂ→Mob G)(H:Mob G): Prop:=∃ g:ℂ→Mob G,∃ R:ℝ,0<R ∧ Hol (disc R) g ∧ g=ᶠ[dotty] f ∧ g 0=H
abbrev Live (f:ℂ→Mob G): Prop:=∃ H:Mob G, Lift f H
def slip (f:ℂ→Mob G)(H:Mob G)(x:ℂ): Mob G:= x⁻¹ • (f x-H)
namespace Lift
lemma trim (h:Hol (disc R) f)(hr:0<R): Lift f (f 0):= ⟨f,R,hr,h,EventuallyEq.refl .., rfl⟩
lemma congr (h:Lift f F)(he:f=ᶠ[dotty] g): Lift g F:=by obtain ⟨p,R,hr,h,Hx,Hz⟩:=h; exact ⟨p,R,hr,h,Hx.trans he,Hz⟩
lemma hols (h:Lift f F): Live (slip f F):= by
    obtain ⟨g,R,hR,h,ht,rfl⟩:=h; refine ⟨_,Lift.congr (trim (HolG h hR) hR) ?_⟩; filter_upwards [ht,dotty_non] with i hi hI; unfold slip; rw [hung hI,hi] -- hi xf def Prop
end Lift
end YM.MS.Shine
