import YM.MSbar.Scale.App
import YM.MSbar.Counter.Winter
/-! Momentum-dimensional operator and polynomial locality of the zero grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Scale
open Dim Symbol Domain Diagram Super Loops Function Set Filter Flight Counter
open scoped Topology BigOperators ContDiff Classical
variable {C:Type}{W: Edition C}{m j n:ℕ}{U:Set ℂ}{d:Bit} {f g:Vertex C}{w:Words C m}{F:Functionals C}

abbrev Mass (C:Type) := Multiset C→ℂ
def tick (A:Mass C)(f:Vertex C) : Vertex C:= apply_at (fun t h=> Flight.flight (A t) h 1) f
variable {A:Mass C} (hf:Live W d f)(hk: ∀ σ, Land (A σ- n))
include hf
lemma tick_add (hg:Live W d g): Scale.tick A (f+g)=Scale.tick A f+Scale.tick A g:= by funext m t; unfold Scale.tick apply_at; dsimp only; rw [ray_add,Flight.add (great_ray hf _) (great_ray hg t)]; rfl -- include hf
lemma tick_scale (c:ℂ): Scale.tick A (c•f)=c•Scale.tick A f:= by funext m t; unfold Scale.tick apply_at; dsimp only; rw [ray_scale,Flight.scale (great_ray hf _)]; rfl
lemma tick_rays : ray (Scale.tick A f) w=flight (A (skin w)) (ray f w):=by
    by_cases he: channel w=0
    · funext x; rw [ray,if_pos he,Scale.tick,apply_at,drag_skin,arms he,through (great_ray hf w) x]; unfold pull; rw [one_mul]
    rw [show ray f w=0 from funext fun x=>by simp [ray,he]]; rw [blank]; exact funext fun t=> by simp [ray,he]
omit hf in
@[simp] lemma tick_zero(A:Mass C):Scale.tick A 0=0:=by funext n t; change flight _ _ 1=_; rw [ray_zero,blank]; rfl
omit hf in
private lemma fares {G:ℂ→Mass C}(he:∀ t,DifferentiableOn ℂ (fun z=>G z t) U)(hu:IsOpen U)(ht:U≠univ)(h:Bright U W d F): Bright U W d (fun z=> Scale.tick (G z) (F z)):= by
    refine lined (A:=fun t z h=> flight (G z t) h 1) (fun t z hz=> great_chart (fun h H=>congr_fun (Flight.add h H) 1) (fun c {_} h=>congr_fun (Flight.scale h c) 1)) ?_ hu ht h
    intro E i1 i2 i3 c g hg
    let a(t:E):= (t,(1:ℝ)); let R(t:ℂ × (E × ℝ)):= t.2.2
    have hw:a.HasTemperateGrowth:= by unfold a; fun_prop
    have hR:AH U (fun p:ℂ ×(E × ℝ)=>(R p:ℂ)):= AH.param_tame (great_cast.comp tame_projR)
    let L:= (AH.holomorphic (X:=E×ℝ) hu (he c)|>.mul hg).sub (hR.mul (hg.rad_deriv hu)); exact L.arguments hw -- attitude
omit hf in
lemma ray_shift {G:ℂ→Mass C}(he:∀ t,DifferentiableOn ℂ (fun z=>G z t) U) [Profit U](h:Price n U W d F): Price n U W d (fun z=>Scale.tick (G z) (F z)):=by
    have ⟨X,hX,hQ⟩:= h
    exact ⟨_,fares he Profit.pub Profit.proper hX,fun z hz=>by rw [← hQ hz,swell_inner,swell_inner,tick_scale (h.alive hz)]⟩
lemma tick_live : Live W d (Scale.tick A f):= devote (W:=W) (U:=disk) (fares (G:=fun _=>A) (fun _=> differentiableOn_const _) Profit.pub Profit.proper (cold hf))
namespace Inertia
-- resonance/support
variable {P:Multiset C→ℕ} {M:Multiset C→ℤ} -- conversion via `.of`. `Admiss`.
def tangent (A:Mass C) (f:Vertex C) := ∀ i (x:Words C i), Approved (A (skin x)) (ray f x)
lemma projects : tangent A (Scale.tick A f):= fun i x=> by rw [tick_rays hf]; exact range_approved (great_ray hf x)
lemma hollow (he:Scale.tick A f=0) (ht:tangent A f): f=0:=by
    funext n w; have huv:=tick_rays (A:=A) (w:=w) hf; rw [he,ray_zero] at huv
    let i:ℕ:= ↑(Nat.ceil ((A (skin w)).re +2)); have hx : (A (skin w)).re+2 ≤ (i:ℝ):= Nat.le_ceil _
    have h:= Flight.unique (ht _ w) (great_ray hf w) huv.symm (n:=i) (by simp only [Land, Complex.sub_re, Complex.natCast_re]; linarith)
    change f n w=0; rw [← ray_center (live_cell hf), h]; rfl
lemma locality (he: Scale.tick (fun t=>(M t:ℂ)) f=0) (t:ℝ) : ray f w t= if M (skin w)<0 then 0 else ((t:ℂ)^((M (skin w)).toNat))*f m w:=by
    let i:= M (skin w); have h:= Eq.symm (tick_rays (A:=fun t=> (M t:ℂ)) (w:=w) hf); rw [he,ray_zero] at h; split_ifs with hl
    · change (i<0) at hl; have hp: (i:ℝ)<0:= by exact_mod_cast hl
      have ht: Approved (i:ℂ) (ray f w):= by intro x hx; apply_fun Complex.re at hx; simp only [Complex.natCast_re,Complex.intCast_re] at hx; linarith [show (0:ℝ) ≤ ↑x by positivity]
      rw [Flight.unique ht (great_ray hf w) h (n:=3) (by simp only [Land, Complex.sub_re,Complex.intCast_re,Complex.natCast_re]; norm_num; linarith)];rfl
    have hh : ((M (skin w):ℤ):ℂ)= ↑(M (skin w)).toNat:= by exact_mod_cast (Int.toNat_of_nonneg (le_of_not_gt hl)).symm
    rw [hh] at h; exact (Flight.local_taylor (great_ray hf _) _ h t).trans (congr_arg (fun z=> _*z) (ray_center (live_cell hf))) -- args
end Inertia
end YM.MSbar.Scale
