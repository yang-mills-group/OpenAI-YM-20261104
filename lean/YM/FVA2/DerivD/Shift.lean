import YM.FVA2.DerivD.Force
/-!
# Spatial derivative identities for the full formal products

Implement by mark substitution. `ProperS` at tuple of positions x and assigned
differentiation indices, prove held-out independence and the pointwise rule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Smooth Lifetime Smooth.Slots MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom MS.Tide MS.Momentum
open O O.Lives
open scoped Topology ContDiff BigOperators Interval
variable {W I J: Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable [LinearOrder W][Fintype W]
variable {A:MS_Data G M}{u:W→Rake.Label b}{a:ℝ}{s t:Steps W}{q:Draw W}{E:Type}
-- Leibniz for Rides.Bouquet.Induction via under-origin logic.
abbrev Stamp (W:Type):= Steps W→Draw W→ Finset W→ Book.Convolve.T ℂ
variable {f g:Stamp W}
def ProperS (s:Steps W)(x:Draw W)(f:Stamp W): Prop:= ∀ i k, Rides 1 i s (fun t p=> f t p i k) x ∧ held s i (fun t=> f t x i k)
lemma zeroT (x:ℂ)(v:Steps W)(q:Draw W): Rides 1 ∅ v (fun _ _=>x) q:= by unfold Rides; apply HasFDerivAt.congr_fderiv ( hasFDerivAt_const x q ) _; unfold Abroad.jet; simp
lemma ProperS.product (hP:ProperS s q f)(hX:ProperS s q g) : ProperS s q (fun i p=> ( Trunk.stack ( marked W ) ).core ( f i p ) (g i p)):= by
    intro i k; have hh (a:Steps W)(p:Draw W): ( Trunk.stack ( marked W ) ).core ( f a p ) (g a p) i k=∑ u∈subs i,∑ j∈ antidiagonal k,f a p u.1 j.1*g a p u.2 j.2:= by change (∑ u∈ subs i, Trunk.core ( f a p u.1 ) ( g a p u.2 ) ) k=_; simp only [ Finset.sum_apply ]; rfl
    simp_rw [hh]; constructor
    · exact Rides.sum _ _ (fun u hu=> Rides.sum _ _ (fun j _=> Rides.prices ( ( joins.mp hu ).2 ) ( ( joins.mp hu ).1.symm ) ( hP _ _|>.1 ) ( hX _ _|>.1 ) (hP _ _|>.2) ( hX _ _ |>.2 )))
    intro u hu; apply Finset.sum_congr rfl; intro i' hi; obtain ⟨ht,hx⟩:= joins.mp hi; obtain hz:Smooth.patch i'.1∪Smooth.patch i'.2=Smooth.patch i:= by rw [ ← ht ]; unfold Smooth.patch; rw [ Finset.union_product ]
    exact Finset.sum_congr rfl fun _ _=> congr_arg₂ ( ·*· ) ( hP _ _ |>.2 u (fun k=> hu ( hz ▸ mem_union.mpr (Or.inl k) ))) ( hX _ _|>.2 u (fun k=> hu ( hz ▸ mem_union.mpr (Or.inr k) )))
lemma ProperS.pow (n:ℕ)(h:ProperS s q f): ProperS s q (fun a p=> ( Trunk.stack ( marked W ) ).power ( f a p ) n):= by
    induction n with
    | zero=> intro i k; refine ⟨?_,fun _ _=> rfl ⟩; by_cases hi:i=∅; subst i; exact zeroT _ _ _; unfold power stack refineV; simp [show i≠(marked W).origin from hi]; exact Rides.zeroS s 1 i q
    | succ n ih=> exact h.product ih
lemma ProperS.full (h:ProperS s q f): ProperS s q ( fun v p=> bouquet ( f v p )):= by
    intro i k; unfold bouquet Cheer Actors.cheers; simp_rw [ Finset.sum_apply ]; constructor; · exact Rides.sum _ _ (fun a _=> (h.pow a i k|>.1).along _ );
    intro u hu; exact Finset.sum_congr rfl fun a _=> congr_arg ( Actors.phase a * · ) ( ( h.pow a i k ).2 u hu )
end YM.FVA2.DerivD
