import YM.RG12.Alidade.Taper
import YM.RG12.Alidade.Fades
/-! # Scheduling fitness on this calendar and clock for a k-order bridge -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Lattice RG Wilson Source Real Frames Commission Rail
open Next.Rank Next.Rank.Perch Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}(h:G.Simple){φ: Filter UVIndex}[φ.NeBot]{M:∀ d,ℕ→RepChart C d}(hC:C.Makes)(hO:Observing C hC φ M)
local notation "Y"=> C.path.levels
local notation "χ"=> C.path.levels.clock.hatBeta
local notation "meter"=> C.path.levels.clock.monitor
local notation "clk"=>epoch C.path.levels
local notation "σ"=>G.slopeConstant
/-- pins calculations to one limit of the actual expansion parameters from regulatorRun,
using same reader and refinement needed by Cast prices. Don't infer PT comparison from any
UV analytic statement here; can satisfy financial ratios by calibrated exact coupling OR this
ultrafilter capture. Avoidance of scheme confusion etc.
 -/
structure Spear (φ:Filter UVIndex)(q:ℕ→ℝ):Prop where
    sits (k):Tendsto (fun (x:UVIndex)=>regulatorRun C x.1 x.2 (k+1)) (φ) (𝓝 (q k))
structure Barred (Z:Levels G)(q:ℕ→ℝ)(K:ℝ):Prop where
    positive k:0 < q k
    meters k : q k^2 * Z.clock.hatBeta k ≤ K
lemma Barred.affords {Z:Levels G}{q:ℕ→ℝ}{K:ℝ}(h:Barred Z q K) : 0 < K:=lt_of_lt_of_le (mul_pos (pow_pos (h.positive 0) 2) (by have ht:=Z.fits.delayed 0; exact zero_lt_one.trans ht)) (h.meters 0)
include h hC hO
lemma coupling_price : ∃ q:ℕ→ℝ, Spear (C:=C) (Ultrafilter.of φ) q ∧ Barred (Z:=C.path.levels) q 4 ∧
       ∀ k,(q k)^2 * (χ (k+1)) ≥ 1/2:=by
   let u:=Ultrafilter.of φ; have hu: (u: Filter UVIndex) ≤ φ:= Ultrafilter.of_le _
   have hc(k:ℕ):0 < χ k:=year (Y) _
   let f(k)(x:UVIndex):=regulatorRun C x.1 x.2 (k+1)
   have ht(k): ∀ᶠ x in (u:Filter UVIndex), 0 ≤ f k x ∧  (f k x)^2*χ (k+1) ∈ Set.Icc (1/2:ℝ) 2:=by
      filter_upwards [((hO.grows).mono_left hu).eventually_ge_atTop (k+1)] with x hx
      let y:= C.path.β x.1 x.2 (k+1); have he:0<y:=Overlay.beta_positive hC.wilson hx
      obtain ⟨hh,hv⟩:= (hC.wilson.represents x.1 x.2 (k+1) hx).band
      unfold f regulatorRun; rw [inv_pow,Real.sq_sqrt he.le,inv_mul_eq_div]
      refine ⟨(inv_pos.mpr (Real.sqrt_pos.mpr he)).le, (le_div_iff₀ he).mpr ?_,(div_le_iff₀ he).mpr ?_⟩ <;> change χ (k+1)/ 2 ≤ y at hh <;> change y ≤ 2*χ (k+1) at hv <;> linarith only [hh,hv] -- simplify nlinarith
   choose q hq using fun k=> ultrafilter_converges u (f k) 2 ((ht k).mono (fun x hx=> by
      rw [Real.norm_of_nonneg hx.1]
      have hs:= delay (Y) (k+1)
      have hh:(f k x)^2*χ (k+1)≤ 2:=hx.2.2
      nlinarith only [hx.1,(mul_le_mul_of_nonneg_left hs (sq_nonneg (f k x))),hh]))
   have he(k):1/2 ≤ q k ^2*χ (k+1) ∧ q k^2*χ (k+1) ≤ 2:=
      isClosed_Icc.mem_of_tendsto (((hq k).pow 2).mul_const _) ((ht k).mono fun _ h=> h.2)
   have hQ(k):0 < q k:=by
      have hh:= ge_of_tendsto (hq k) ((ht k).mono fun _ h=>h.1)
      have hl:1/2 ≤ q k^2*χ (k+1):=(he k).1
      by_contra! he; rw [show q k=0 from he.antisymm hh] at hl; linarith only [hl]
   refine ⟨q,⟨hq⟩,⟨hQ,fun k=> ?_⟩,fun k=>(he k).1⟩
   exact (mul_le_mul_of_nonneg_left (year_mono (Y) h k.le_succ) (sq_nonneg _)).trans ((he k).2.trans (by norm_num))

omit hC hO in
lemma ratio_throttle (w:ℕ): ∀ᶠ i in atTop, (meter i)^w ≤ Real.sqrt (χ i):=by
   filter_upwards [(year_late (Y) h).eventually (YM.Vac.Numbers.cost (w:ℝ) (1/2) (by norm_num))] with i hi
   rw [Real.rpow_natCast,←Real.sqrt_eq_rpow] at hi
   exact hi
-- arbitrary meter exponents, true parameter throughout
omit hC hO in
lemma allowances {q:ℕ→ℝ}{H:ℝ}(hZ:Barred (Z:=(Y)) q H)(o:ℕ): Tendsto (fun k=> Real.sqrt (q k)* meter k^o ) atTop (𝓝 0):=by
   have ht:=hZ.positive
   let f(k:ℕ):= Real.sqrt (q k)* (meter k)^o; have hf(k:ℕ):0≤f k:=by unfold f; exact mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans (one_le_pow₀ (monitor_big _ _)))
   let x(k:ℕ):=Real.sqrt (χ k);have hx(k):= Real.sqrt_pos.mpr (year (Y) k);have hz:= Real.tendsto_sqrt_atTop.comp (year_late (Y) h)
   have hl:Tendsto (fun k=>f k^4) atTop (𝓝 0):=by
      apply squeeze_zero' (g:=fun k=>H/x k)
      · filter_upwards with k using pow_nonneg (hf k) 4
      · filter_upwards [ratio_throttle (C:=C) h (o*4)] with k hh
        have he': Real.sqrt (q k)^4=q k^2:=by rw [show 4=2*2 by norm_num,pow_mul,Real.sq_sqrt (ht k).le]
        unfold f; rw [mul_pow,←pow_mul,he',le_div_iff₀ (hx k)]
        calc _ ≤ q k ^2*Real.sqrt (χ k)*x k:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (sq_nonneg _)) (by unfold x; exact (hx _).le)
             _ = q k^2*χ k:= by rw [mul_assoc,show Real.sqrt (χ k)*x k=_ from by unfold x; exact Real.mul_self_sqrt (year (Y) k).le]
             _ ≤ H:=hZ.meters _
      exact (tendsto_const_nhds (x:=H)).div_atTop hz
   have he:= Real.continuous_sqrt.continuousAt.tendsto.comp (Real.continuous_sqrt.continuousAt.tendsto.comp hl); simp only [Real.sqrt_zero] at he
   exact he.congr (fun k=> by dsimp only [Function.comp_apply]; rw [show 4=2*2 by norm_num, pow_mul,Real.sqrt_sq (sq_nonneg _),Real.sqrt_sq (hf k)])
omit hC hO in
lemma eventual_bar {q:ℕ→ℝ}{H:ℝ}(hZ:Barred (Z:=(Y)) q H): ∀ o:ℕ,∀ᶠ k in atTop, let t:=q k;let s := meter k^o; t ≤ 1∧ s*(t+t^2) ≤ 1/2∧ 27*s^3*Real.sqrt t ≤ 1:=by
   intro o
   have he:= allowances h hZ
   filter_upwards [(he 0).eventually (ge_mem_nhds (by norm_num:0<(1:ℝ))), (he o).eventually (ge_mem_nhds (by norm_num:0 < (1/4:ℝ))), (he (o*3)).eventually (ge_mem_nhds (by norm_num:0 < (1/27:ℝ)))] with k h1 h2 h3 t s
   have ht:=hZ.positive k; have hs:0 ≤ s:=zero_le_one.trans (one_le_pow₀ (monitor_big ..))
   let x:= Real.sqrt t;have hx:=Real.sq_sqrt ht.le
   have hf: x ≤ 1:= by simpa only [pow_zero,mul_one] using h1
   have hh:0 ≤ x:=Real.sqrt_nonneg _
   have hb:t ≤ 1∧t ≤ x:=by change x^2=t at hx; constructor<;>nlinarith only [hx,hf,hh]
   rw [pow_mul] at h3
   change x*s^3 ≤ 1/27 at h3
   change x*s ≤ 1/4 at h2
   refine ⟨hb.1,?_,?_⟩
   · nlinarith only [hb.1,mul_le_mul_of_nonneg_left hb.1 ht.le, mul_le_mul_of_nonneg_left (show t+t^2 ≤ 2*x from by nlinarith only [ht,hb.1,hb.2]) hs,h2]
   linarith only [h3]

end YM.RG12.Alidade
