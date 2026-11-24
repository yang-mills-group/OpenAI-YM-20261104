import YM.FVA2.Lambda.Extract
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
/-!
# Continuum down initial data at top ranks

 Shift t by scaling and tack on polynomial in log µ; smooth per chart at the frozen
 interpolation nodes. Shows t→−∞ *pointwise at fixed external momenta* total fieldDim > 4
 gives 0; and fieldDim ≥ 4, including marginal, the difference from local term tends to 0.
 Prior rank Bound's upper rank means no self-loop on these if top. None of these asymptotics
 are large-cutoff claims. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Canvas
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Local.Physical MS.Outlook MS.Halo MS.Alps MS.City MS.Book.Program MS.Logarithm MS.High.Knobs
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{k m n:ℕ}
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
abbrev onset (w:List (Lane4 G)): List (Lane4 G):= sail (ray w) 0
variable (x t:ℝ)(w:List (Lane4 G))
@[simp] lemma on_len : (onset w).length=w.length:= by rw [onset,sail_len,ray_len]
@[simp] lemma on_mass : fieldDim wfield (onset w)=fieldDim wfield w:=by rw [onset,sail_dim,ray_dim];
@[simp] lemma on_fx : onset (w.map (fun i=> (i.1,t • i.2)))= onset w:= by simp [onset, Function.comp_def ];
@[simp] lemma sr_onset : sr t (onset w)= onset w:= by simp [onset, Function.comp_def,sr];
lemma closed_onset : Course true ( onset w ):= fun _=> by rw [ onset,sail_net ]; simp
lemma poly_bot (p:Polynomial ℝ): Tendsto (fun t:ℝ=> exp t * p.eval (x+t)) atBot (𝓝 0) := by
    obtain hp:= ( Polynomial.tendsto_div_exp_atTop (p.comp (Polynomial.C x - Polynomial.X)) ).comp ( tendsto_neg_atBot_atTop (G:=ℝ)) ; simpa [sub_neg_eq_add, Function.comp_def, exp_neg,mul_comm,div_eq_mul_inv] using hp
lemma poly_bot_dim (p:Polynomial ℝ){i:ℤ}(hi:0 < i): Tendsto (fun t:ℝ=> exp t ^ i * p.eval (x+t)) atBot (𝓝 0) := by
    obtain hp:= ( tendsto_exp_atBot.pow ((i-1).toNat) ).mul (poly_bot x p); rw [mul_zero] at hp; apply hp.congr; intro u; conv_rhs => arg 1; rw [show i= ↑(i-1).toNat +1 from (by omega), zpow_add₀ ( exp_pos u ).ne', zpow_natCast,zpow_one]
    rw [mul_assoc]
include hm
lemma scales : high X n (x,t) w=( exp t ^ (fieldDim wfield w-4) ) • ( high X n (x+t,0) (sail ( ray w ) ( exp t )) ):= by
    rw [Complex.real_smul,ray_go]; unfold high Archive; rw [ Port.Bx4 (ζ:=t) ( Host.host ( gang ( hm n ) ) ), sub_self ]; rfl
-- interpolation of Archive
lemma pts : ∃ N:ℕ, ∀ (r t:ℝ)(l:List (Lane4 G)), high X n (r,t) l= ∑ i∈ Finset.range N,(Logarithm.plate N i).eval r • ( high X n ( (i:ℝ),t ) l):= by
   obtain ⟨N,h⟩:= ( Outlook.dock hm wisdom ).master.poly n; refine ⟨N,fun r t l=>?_⟩; obtain he:= congr_fun (congr_fun (interpret h r) t) l; unfold Logarithm.evaluate at he; simp only [Finset.sum_apply] at he; exact he
variable {w}(hc: Course true w)(hp: 0<w.length) (hn:1≤n)
include hc hp hn
lemma steam (s:ℝ) : HasDerivAt (fun t=> high X n (x,t) w) (trigger X n (x,s) w) s:= by
    obtain ht:= ( ( Outlook.dock hm wisdom ).master.road ℝ (ray w) n hn ( fun _=> (ray_len w).symm ▸ hp ) ( ray_course hc ) ).2.2 x s 1 0
    obtain hL:= (ContinuousMultilinearMap.apply ℝ _ ℂ (fun _ : Fin 0=> (1:ℝ))).hasFDerivAt.comp_hasDerivAt _ ht
    simp only [Function.comp_def, ContinuousMultilinearMap.apply_apply,iteratedFDeriv_zero_apply,Domain.tape,Chart, ray_sail] at hL; exact hL
lemma down (hV:4<fieldDim wfield w): Tendsto (fun t:ℝ=> high X n (x,t) w) atBot (𝓝 0):= by
    obtain ⟨N,h⟩:= pts (n:=n) hm; let Q:=Finset.range N; let v i:ℝ→ℂ:= fieldVal (high X n ( (i:ℕ),0 )) (ray w); let a:=fieldDim wfield w-4; let f (i:ℕ) (t:ℝ):= ( exp t ^ a * ( Logarithm.plate N i ).eval (x+t)) • (v i (exp t))
    have ht (i:ℕ): Tendsto (f i) atBot (𝓝 0):= by obtain hx:= ( smooth hm _ hc hp hn ( (i:ℝ),0 ) ).continuous.tendsto 0; obtain hu:= ( poly_bot_dim x ( Logarithm.plate N i ) (i:=a) (by unfold a; omega) ).smul (hx.comp tendsto_exp_atBot); rw [zero_smul] at hu; exact hu
    obtain h':= tendsto_finsetSum Q (fun i _=> ht i); rw [Finset.sum_const_zero] at h'; apply h'.congr; intro t; rw [ scales hm, h (x+t) 0 ]; unfold f Q at *; simp only [smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [smul_smul]; rfl
lemma fringes (hd:4≤fieldDim wfield w): Tendsto (fun t:ℝ=> high X n (x,t) w-high X n (x,t) (onset w)) atBot (𝓝 0):= by
    rcases hd.eq_or_lt with hu|hu
    swap; · simpa only [sub_zero] using (down hm x hc hp hn hu).sub (down hm x ( closed_onset w ) (by rw [on_len]; exact hp) hn (by rwa [on_mass]))
    obtain ⟨N,h⟩:= pts (n:=n) hm; let Q:=Finset.range N; let v (i:ℕ):ℝ→ℂ:= fieldVal (high X n ( (i:ℝ),0 )) ( ray w ); let f (i:ℕ) (t:ℝ):= ( exp t * ( Logarithm.plate N i ).eval (x+t)) • ( slope (v i) 0 (exp t) )
    have hf i : Tendsto (f i) atBot (𝓝 0):= by
        have hp : Tendsto (slope (v i) 0) (𝓝[≠] (0:ℝ)) (𝓝 ( deriv (v i) 0 )):= ( show DifferentiableAt ℝ (v i) 0 from ( smooth hm w hc hp hn _ ).differentiable (by simp) 0 ).hasDerivAt.tendsto_slope; obtain hv:= (poly_bot x (Logarithm.plate N i)).smul ( hp.comp (tendsto_exp_atBot_nhdsGT.mono_right ( nhdsGT_le_nhdsNE (0:ℝ) )) ); rw [zero_smul] at hv; exact hv
    obtain he:= tendsto_finsetSum Q (fun i _=>hf i); rw [Finset.sum_const_zero] at he; apply he.congr; intro t; have ht : sail (ray (onset w)) (exp t)=onset w:= by rw [ray_go]; exact sr_onset t w
    rw [ scales hm x t w,scales hm x t (onset w),ht,on_mass,← hu,sub_self,zpow_zero,one_smul,one_smul,h (x+t) 0 _,h (x+t) 0 _, ← Finset.sum_sub_distrib ]; apply Finset.sum_congr rfl; intro i _; unfold f; rw [slope_def_module,smul_smul, sub_zero, mul_comm (exp t),mul_assoc, mul_inv_cancel₀ (exp_pos t).ne',mul_one,smul_sub]; rfl
end YM.FVA2.Lambda.Canvas
