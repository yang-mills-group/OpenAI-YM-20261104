import YM.MS.Hem.Foundation
/-!
# UV at fixed R MS counterterms; Euler through Laurent jets
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Pearl
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W X F: Mob G} {x:ℂ} {b:Bool} {n ℓ m:ℕ} {h:ℕ}{s:ℝ}
def burn (a:ℂ)(F:Mob G): Mob G:= fun m l=> deriv (fun t=> plow a t F m l) 0
open Alps.Bench.Forest
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
lemma bump (h:kPrice F)(w:Touch G m E): fieldVal (burn x F m) w=loadC (fieldVal (F m) w) (x+mass w):= by
   funext p; change deriv (fun t=> fieldVal (plow x t F m) w p) 0=_; rw [show (fun t=> fieldVal (plow x t F m) w p)=(fun t=> Alps.Bench.Forest.patch (fieldVal (F m) w) (x+mass w) t p) from funext fun i=> s_p_vector .., ( patch_d ((h m E w).smooth ()) (x+mass w) p 0).deriv]; simp [Alps.Bench.Forest.patch,Alps.amount] -- ambig patch
lemma burn_d (hp:kPrice F) (m:ℕ) (w:Touch G m E) (s:ℝ)(p:E): HasDerivAt (fun t=> fieldVal (plow x t F m) w p) (fieldVal (plow x s (burn x F) m) w p) s:= by
    simp_rw [s_p_vector,bump hp]; exact patch_d ((hp m E w).smooth ()) _ p s
lemma burn_s (hp:kPrice F): Mell.Trail F (burn x F) x:= ⟨fun s m l=>by simpa only [fieldVal,ray_sail] using burn_d (x:=x) hp m (ray l) s 1 ⟩
lemma burn_unique (hp:Mell.Trail F X x)(h:kPrice F): X= burn x F:= by funext m l; simpa only [posing] using (hp.derive 0 m l).unique ((burn_s h).derive 0 m l)
lemma bill_b (x:ℂ){v:I→ Mob G}(h: fell 0 1 v): fell 0 1 (fun i=> burn x (v i)):= by
    intro m E _ _ _ w; simp_rw [bump (fee h _)]; let f (i:I):= fieldVal (v i m) w; let A:= ContinuousLinearMap.mul ℝ ℂ (x+mass w); have hf:= h m E w; have hu : veg 0 (fun i=>fderiv ℝ (f i)) 1:= by simpa only [cheap_length,mul_one,f] using hf.fderiv;
    apply Costs.add (hf.L A); convert! Costs.bilinear (ContinuousLinearMap.apply ℝ ℂ (E:=E)) (uGrab (Bench.Forest.at_id (E:=E)) (fun _:I=>())) hu using 1; ext; simp
lemma burn_f (h:kPrice F)(x:ℂ): kPrice (burn x F):= bill_b x h
lemma burn_hol (x:ℂ){R:ℝ}{f:ℂ→ Mob G}(hf:Hol (disc R) f): Hol (disc R) (fun i=> burn x (f i)):= by
    refine ⟨ fun c R ht hp=> bill_b x (hf.price c R ht hp), fun m l i hi=> ?_⟩; let w := ray l; -- remove placeholder
    let y:ℂ→ ℝ→ℂ:= fun z=>fieldVal (f z m) w; let U(z:ℂ)(p:ℝ):= loadC (y z) (x+mass w) p; have H z (hz:z∈disc R) : burn x (f z) m l = U z 1:= by obtain ht := congr_fun ( bump (x:=x) (hf.link hz isOpen_ball) w) 1; exact Eq.trans (congr_arg (burn x (f z) m) (ray_sail l).symm) ht
    refine DifferentiableAt.congr_of_eventuallyEq (f:=fun z=> U z 1) ?_ ( (show ∀ᶠ p:ℂ in 𝓝 i,p∈disc R from isOpen_ball.mem_nhds hi).mono fun i hi=> H i hi); have he:= billJet (f:=y) (key_fall hf w) (j:=1) 1 (fun _=>1); simp only [iteratedFDeriv_one_apply] at he; exact ( (key_fall hf w|>.root 1 i hi).const_mul _).add (he i hi)
lemma burn_raise (z:ℂ)(h:kPrice F) : burn (x+z) F=burn x F+z • F:= by
    funext m l; obtain hL:= bump (x:=x) h (ray l); rw [← ray_sail l]; change fieldVal (burn (x+z) F m) (ray l) 1 =fieldVal (burn x F m) (ray l) 1+ z*fieldVal (F m) _ 1; rw [bump h,hL]; simp only [loadC]; ring
lemma burn_mul (x c:ℂ)(hp:kPrice F): burn x (c • F)= c • burn x F:= by
   exact Eq.symm (burn_unique ((burn_s hp).smul c) (show kPrice (c • F) from (by convert! fall_scale (U:=fun _:Unit=>c) hp (const_sc ..) using 1; ext; simp)))
lemma burn_add (x:ℂ)(h:kPrice F)(ht:kPrice X): burn x (F+X)=burn x F+burn x X:= Eq.symm (burn_unique ((burn_s h).plus (burn_s ht)) (fall_add h ht))
lemma burn_sub (x:ℂ)(h:kPrice F)(ht:kPrice X): burn x (F-X)=burn x F-burn x X:= by simp_rw [sub_eq_add_neg,← neg_one_smul ℂ X]; rw [burn_add x h, burn_mul x (-1) ht,neg_one_smul]; convert! fall_scale (U:=fun _:Unit=> (-1:ℂ)) ht (const_sc ..) using 1; ext; simp
-- Lift comm
variable {f:ℂ→Mob G}
lemma burn_lift (h:Lift f F)(x:ℂ): Lift (fun i=> burn x (f i)) (burn x F):= by obtain ⟨g,r,hr,h,Ht,rfl⟩:=h; exact Lift.congr (Lift.trim (burn_hol x h) hr) (Ht.mono fun i hi=> congr_arg _ hi)
lemma burn_pick (h:Pick n f F)(x:ℂ): Pick n (fun i=> burn x (f i)) (burn x F):= by
    induction n generalizing f with
    | zero=> exact burn_lift h x
    | succ n ih=>
       obtain ⟨V,H,H0⟩:=h; refine ⟨ _, burn_lift H x, Pick.congr (ih H0) ?_ ⟩; filter_upwards [Live.price (f:=f) ⟨_, H⟩ ] with i hi; unfold slip; rw [burn_mul x i⁻¹ (show kPrice (f i-V) from fall_sub hi (Lift.price H)),burn_sub x hi (Lift.price H)]
end YM.MS.Pearl
