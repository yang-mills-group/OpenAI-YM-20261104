import YM.FVA2.Wick.Formal
import YM.FVA2.Slice.Body
/-!
# Arithmetic with analytic commuting jets in the super Wick calculus

A `Raw` table doesn't have bounded rank in general. To transmit the actual Wilson vertices, use
`letter` = the Taylor table split into its homogeneous symbol components (formal-order valuation
is exactly leg rank here). Multiplicativity and the Euler map both follow on these actual analytic
germs; not assuming convergence for perturbation series on a regulator sequence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset Filter
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open Formal (overlay)
open scoped BigOperators Topology ContDiff Matrix
variable {A I J E : Type} {p : Sector A}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Gem
variable (e : A→E) (f : E→ℝ)
/-- Taylor jets with valuation=rank. -/
def letter (n:ℕ) := mask (n:ℤ) (ink e f)
local notation "T" => letter e

lemma first : T f 0=coin (↑(f 0):ℂ) := by unfold letter; rw [Nat.cast_zero,mask_zero]; rfl
variable {f} {g : E→ℝ}
lemma good (h:germ f) (he:∀ i,p i=true→e i=0) : T f∈ Formal.OK p := by
  intro i _; exact ⟨sym_mask (ink_s e he h) _, minH (Limit.mod _ _)⟩
lemma add (h:germ f)(hp:germ g) : T (f+g) = T f+T g := by unfold letter; rw [ink_add e h hp]; exact funext fun _=> map_add ..
lemma zero : T (0:E→ℝ)=0:= funext fun i=> by rw [letter,ink_zero,map_zero]; rfl
lemma sub (h:germ f)(hp:germ g) : T (f-g)=T f-T g := by unfold letter; rw [ink_sub e h hp]; exact funext fun _=>map_sub ..
lemma smul (h:germ f) (c:ℝ) : T (c • f) = (c:ℂ) • T f:= by unfold letter; rw [ink_smul e h c]; exact funext fun _=>map_smul ..
lemma sum (s:Finset I) (f:I→E→ℝ)(h:∀ i∈s,germ (f i)) : T (∑ i∈s,f i)=∑ i∈s,T (f i):= by
  funext n; rw [letter,ink_sum _ s h,Finset.sum_apply,map_sum]; rfl
lemma entire (c:ℝ) : T (fun _:E=>c)=Formal.tab (coin (A:=A) (c:ℂ)) := by
  funext i; rw [Formal.tab_value]; split
  next h=> rw [h, first]
  next h=> unfold letter; rw [ink_const e c]; exact rank_off (Rails.coin _) (by omega)
lemma nearby (he:f =ᶠ[𝓝 0] g) : T f=T g := by unfold letter; rw [inkit e he]

variable (hE:∀ i,p i=true→ e i=0)
include hE
lemma times (h:germ f)(hp:germ g) : T (f*g)=overlay p (T f) (T g):= by
  have hT (f:E→ℝ) (x:ℕ) : T f x = rankLevel 0 (ink e f) x := by simp only [rankLevel, letter, add_zero]
  have hZ (F:E→ℝ) : From (ink e F) 0 := fun l hl=> by omega
  funext n; simp_rw [Formal.coeff_prod,hT, pairLevel _ (hZ f) (hZ g), zero_add, ink_mul e hE h hp]
lemma even (f:E→ℝ) : T f∈ Formal.even p := by
  apply Formal.ev.mpr; intro i; exact alone_pure (alone_mask (x:=ink e f) (p:=p) (ink_uses _ _ (fun i (_hi : i ∉ {j|p j=false})=> hE i (by simpa using _hi)) f) _)

omit hE
def Euler (f:E→ℝ) (x:E) := layer x f x
variable {x:E}
lemma Euler_s (h:germ f) : germ (Euler f) :=
    (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_id
lemma balance (h:germ f)(x:E) : layer x (Euler f) =ᶠ[𝓝 0] Euler (layer x f) + layer x f := by
  filter_upwards [h.eventually (by simp)] with y h
  have ht := (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  change fderiv ℝ (fun a=> fderiv ℝ f a a) y x =
    fderiv ℝ (fun a=> fderiv ℝ f a x) y y + _
  rw [(ht.hasFDerivAt.clm_apply (u:=fun x=>x) (hasFDerivAt_id _)).fderiv,
     (ht.hasFDerivAt.clm_apply (u:=fun _=>x) (hasFDerivAt_const x y)).fderiv]
  simp [layer]; rw [h.isSymmSndFDerivAt_of_omega x y]; abel
lemma declock (h:germ f) (l:List A) : ink e (Euler f) l=(l.length:ℂ)*ink e f l:= by
  induction l generalizing f with
  | nil=> simp [ink, Euler, layer]
  | cons i l ih=>
    let g:=layer (e i) f; have he : germ g:= germ_layer h _
    simp only [D_eval i (ink e (Euler f)),inktip, List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [inkit e (balance h _),ink_add e (Euler_s (germ_layer h _)) (germ_layer h _), Pi.add_apply, ih he]
    rw [D_eval i (ink e f), inktip]; ring
lemma clock (h:germ f) : T (Euler f)=Swirl.clock useN (Raw A ℂ) (T f):= by
  funext i l; rw [Formal.time_weight]; unfold letter; by_cases he:(l.length:ℤ)=i; · rw [enough l he, Pi.smul_apply,enough l he, declock _ h l]; rw [ show (l.length)=i from (by omega) ]; rfl
  rw [strange l he,Pi.smul_apply,strange l he,smul_zero]
end Gem
end YM.FVA2.Wick
