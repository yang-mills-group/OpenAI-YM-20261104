import YM.XSpace.Panorama
/-!
# IFT with genuine parameters, regular and locally unique.

Through any horizon. No positivity of *meshed* Gram used here!
Record derivative and bounded inverse on params useful for later orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory Asymptotics
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d:ℕ} {A: Screen G d}
namespace Fray
variable (D:Fray A) (H:A.Prepared)
private theorem invert : ∀ {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f:E→L[ℝ] E}, Bijective f → f.IsInvertible:=by intro E _ _ _ f h; exact ⟨ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.mpr h.1) (LinearMap.range_eq_top.mpr h.2),rfl⟩
private theorem std {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] : ∀ᶠ f:E→L[ℝ] E in 𝓝 1,Bijective f:=by
  filter_upwards [Units.isOpen.mem_nhds (show IsUnit (1:E→L[ℝ] E) from isUnit_one)] with i hi; exact ContinuousLinearMap.isUnit_iff_bijective.mp hi

include H in
lemma pin_inv : (D.delta D.opening).IsInvertible:=by rw [D.unpin H]; exact invert bijective_id

def route (H:A.Prepared) := (show ContDiffAt ℝ ω D.itinerary D.opening from D.fair.contDiffAt).implicitFunction (by simp) (D.pin_inv H)

theorem ground0 : D.route H D.opening.1= D.opening.2:= ContDiffAt.implicitFunction_apply_self ..
theorem terrain : ∀ᶠ x in 𝓝 D.opening.1,D.itinerary (x,D.route H x)=D.itinerary D.opening:= ContDiffAt.eventually_apply_implicitFunction ..
theorem pathway : ∀ᶠ x in 𝓝 D.opening,D.itinerary x=D.itinerary D.opening ↔ D.route H x.1=x.2:= ContDiffAt.eventually_apply_eq_iff_implicitFunction ..
theorem train : ContDiffAt ℝ ω (D.route H) D.opening.1 := ContDiffAt.contDiffAt_implicitFunction ..
theorem destination : Tendsto (D.route H) (𝓝 D.opening.1) (𝓝 0):=by rw [← show D.route H D.opening.1=0 from D.ground0 H]; exact (D.train H).continuousAt

def firstPass (H:A.Prepared) (P:Prediction G d) := (guide G d).symm (D.route H (D.purse P))
lemma guid (P:Prediction G d): guide G d (D.firstPass H P)= D.route H (D.purse P):= (guide ..).apply_symm_apply _
@[simp] lemma pass_free : D.firstPass H (reference G d)=0:=by unfold firstPass; rw [show D.route H (D.purse _)=0 from D.ground0 H,map_zero]

def SetEq (A:Screen G d) (T:Change G d) (P: Prediction G d):Prop:= A.D (recruit (stand T) P)= A.D (reference G d)
lemma means (v:Change G d) (P:Prediction G d): SetEq A v P ↔ D.itinerary (D.purse P,guide G d v)=D.itinerary D.opening:=by
  rw [opening,way,way,box,box,LinearEquiv.symm_apply_apply,map_zero,stand0, (guide G d).injective.eq_iff]; rfl

variable {ι : Type*} {u:Filter ι} (P:ι→Prediction G d)
def Via := Tendsto (fun i=> D.purse (P i)) u (𝓝 D.opening.1)
variable {P} (h:D.Via P (u:=u))
lemma metric_jumps (V:Change G d) (x:Sec G d): tableD G d (stand V x)= (err ((stand V).restrictScalars ℝ)) (tableD G d x):=(err_apply ((stand V).restrictScalars ℝ) x).symm
private theorem ways_stood (f:Sec G d): Continuous (fun v:MoveSpace G d => tableD G d (box v f)):= by
  let L : MoveSpace G d→ₗ[ℝ] RSpace G d:= { toFun v:= tableD G d (((guide G d).symm v).val f), map_add' u v:=by rw [map_add]; exact map_add (tableD G d) _ _, map_smul' a v:=by rw [map_smul]; exact map_smul (tableD G d) _ _ }
  simp_rw [box,stood,map_add]; exact (continuous_const (y:= tableD G d f)).add L.continuous_of_finiteDimensional

theorem safe_pegs : ∀ᶠ v:MoveSpace G d in 𝓝 0,Bijective (box v):=by
  let f (v:MoveSpace G d):= err ((box v).restrictScalars ℝ); let a:= tableD G d; have he v p : a (box v p)= f v (a p):= metric_jumps _ p
  have hh: Continuous f:=by
    apply continuous_clm_apply.mpr; intro p; obtain ⟨u,rfl⟩:= a.surjective p; simp_rw [← he]; exact ways_stood u
  have hv:f 0=1:=by ext1 p; obtain ⟨u,rfl⟩:=a.surjective p; rw [← he, box,map_zero,stand0]; rfl
  filter_upwards [hh.continuousAt.tendsto.eventually (show ∀ᶠ k:RSpace G d →L[ℝ] RSpace G d in 𝓝 (f 0),Bijective k by rw [hv]; exact std)] with v hk; convert a.symm.bijective.comp (hk.comp a.bijective) using 1; ext1 i; rw [Function.comp_apply,Function.comp_apply,← he,a.symm_apply_apply]
lemma freePegs : Bijective (stand (0:Change G d)):=by rw [stand0]; exact bijective_id
lemma continuous_steps : Continuous D.delta:=(D.fair.continuous_fderiv (by simp)).clm_comp continuous_const
include H in
theorem unhit : ∀ᶠ v in 𝓝 D.opening,(D.delta v).IsInvertible:=
  ((D.continuous_steps).continuousAt.tendsto.eventually (show ∀ᶠ k:MoveSpace G d→L[ℝ] MoveSpace G d in 𝓝 (D.delta D.opening), Bijective k by rw [D.unpin H]; exact std)).mono fun _ hk=> invert hk
lemma upright (U:Prediction G d) (x:Change G d) (h: (D.delta (D.purse U,guide G d x)).IsInvertible): Bijective (slope A x U):=by
  let a:= guide G d; convert a.symm.bijective.comp (h.bijective.comp a.bijective) using 1; funext t; simp_rw [Function.comp_apply]; unfold a; rw [order, align, LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]

include h in
lemma passed : ∀ᶠ i in u,SetEq A (D.firstPass H (P i)) (P i):= by
  filter_upwards [h.eventually (D.terrain H)] with i hi; rw [D.means,D.guid]; exact hi
include h in
lemma turns_approach : Tendsto (fun i=> guide G d (D.firstPass H (P i))) u (𝓝 0) := by simp_rw [guid]; exact (D.destination H).comp h
include h in
theorem stand_sure : ∀ᶠ i in u,Bijective (stand (D.firstPass H (P i))):= ((D.turns_approach H h).eventually (safe_pegs (G:=G) (d:=d))).mono (fun i hi=> by rwa [box,LinearEquiv.symm_apply_apply] at hi)
include h in
theorem still : ∀ᶠ i in u,Bijective (slope A (D.firstPass H (P i)) (P i)):= by
  filter_upwards [(Tendsto.prodMk_nhds h (D.turns_approach H h)).eventually (D.unhit H)] with i hi; exact D.upright _ _ hi
include h in
theorem unmoor (v:ι→Change G d) (he:Tendsto (fun i=> guide G d (v i)) u (𝓝 0)):
    ∀ᶠ i in u,SetEq A (v i) (P i) ↔ D.firstPass H (P i)=v i:=by
  filter_upwards [(Tendsto.prodMk_nhds h he).eventually (D.pathway H)] with i hi; rw [← (guide G d).injective.eq_iff,D.means,D.guid]; exact hi

-- uniform inverse derivatives used at positive formal orders
include h in
theorem toll : Tendsto (fun i=> (D.delta (D.purse (P i),guide G d (D.firstPass H (P i)))).inverse) u (𝓝 (1:MoveSpace G d →L[ℝ] MoveSpace G d)) := by
  have he : (D.delta D.opening).inverse=1:=by rw [D.unpin H]; exact ContinuousLinearMap.inverse_equiv (.refl ℝ _)
  rw [← he]; exact (((D.pin_inv H).contDiffAt_map_inverse (n:=1)).continuousAt).tendsto.comp (D.continuous_steps.continuousAt.tendsto.comp (Tendsto.prodMk_nhds h (D.turns_approach H h)))
end Fray
end YM.XSpace.Normalize
