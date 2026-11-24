import YM.FormalBulk08.First.Cut

/-! Interface to proposed top cutoff: exponential-flat bound uniform
admitted Λ geometry any finite powers. No assertion usable on actual
remainders. Include comparison to actual path coupling positive branch band. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.First
open Function Filter Set MeasureTheory Lattice RG Exterior Wilson Precision
open Stationary hiding shine Rays
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine Dove North Aster
open Next.Foundations PhysicalNext.Repeat.Legato
open Borough RG.Supply Push.PriceCompiler Dove.Lab
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{A:Levels G}{C:Family G}{W:Borough.Window G K}
lemma payroll_s (A:Levels G)(h:G.Simple)(q:ℝ)(hp:1<q)(θ:ℝ)(hw:0 < θ) (e:ℕ)(b a:ℝ) (hb:0≤b): ∀ᶠ i in atTop, b * (Lambda A i)^e*ratioR A.S (i+endV A i ((Lambda A i)^q)) i θ ≤ Real.exp (-(a * Lambda A i)):= by
    have hq (i):0<Lambda A i:=zero_lt_one.trans_le (lambda_large A i)
    have hv (i):0<(Lambda A i)^q:= Real.rpow_pos_of_pos (hq i) _
    let L:= Lambda A
    have he:Tendsto (fun i=> θ* L i ^(q-1)) atTop atTop:= Tendsto.const_mul_atTop hw ((tendsto_rpow_atTop (by linarith : 0<q-1)).comp (lambda_slope A h))
    have ht:Tendsto (fun i=>b*(L i)^e*Real.exp (-L i)) atTop (𝓝 0):= by
        simp_rw [mul_assoc]; simpa only [mul_zero,Function.comp_def] using! ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero e).comp (lambda_slope A h)).const_mul b
    filter_upwards [ht.eventually_le_const (show 0 < (1:ℝ) from zero_lt_one),he.eventually_ge_atTop (1+a)] with i hs hz
    let s:=sowing A.S i (i+endV A i ((L i)^q)); have he : θ*s≥ (1+a) * L i:= by
        refine le_trans (mul_le_mul_of_nonneg_right hz (hq i).le) (?_); change θ * L i ^ (q-1) * L i≤ _; rw [mul_assoc,←Real.rpow_add_one (hq i).ne',sub_add_cancel]; exact mul_le_mul_of_nonneg_left (endV_peak _ _ (hv i)).2.1 hw.le
    rw [←ring_out];change _*_*Real.exp (-θ*s) ≤ Real.exp (-(a*L i)); calc
       _ ≤ b*(L i)^e*Real.exp ( - L i - a* L i):= mul_le_mul_of_nonneg_left (Real.exp_monotone (by nlinarith only [he])) (mul_nonneg hb (pow_nonneg (hq i).le _))
       _ = b*(L i)^e*Real.exp (-L i)*Real.exp (-(a*L i)):= by rw [mul_assoc (b*_ ),←Real.exp_add,sub_eq_add_neg]
       _ ≤ _:= mul_le_of_le_one_left (Real.exp_pos _).le hs
-- all admitted N' and PERIOD q, arbitrary powers only
open Pert.Asymptotics
lemma hatted (C:Family G)(p:C.Makes)(i N q:ℕ)(h:i≤ N): Real.exp (-Lambda C.path.levels i) ≤ regulatorRun C N q i:= by
   let A:= C.path.levels; let b:=A.clock.hatBeta i; have hv : 1 < b:= A.fits.delayed i; let y:=C.path.β N q i; obtain ⟨hp,hP⟩:b/2≤y∧ y≤2*b:= (p.wilson.represents _ _ _ h).band
   have hb:0<b:=by linarith
   have hy:0<y:=by linarith
   change Real.exp (-(2+Real.log b)) ≤(Real.sqrt y)⁻¹; rw [Real.exp_neg, Real.exp_add,Real.exp_log hb]; apply inv_anti₀ (Real.sqrt_pos.2 hy); have he : 2≤Real.exp 2:= by linarith [Real.add_one_le_exp (2:ℝ)]
   refine (?_ : Real.sqrt y≤ 2*b)|>.trans (mul_le_mul_of_nonneg_right he hb.le); nlinarith [Real.sq_sqrt hy.le,Real.sqrt_nonneg y]
lemma hearty (p:C.Makes)(hG:G.Simple)(q:ℝ)(hp:1<q)(θ:ℝ)(hw:0 < θ) (d e:ℕ)(b:ℝ)(hb:0≤b) : let N i:=i+endV C.path.levels i ((Lambda C.path.levels i)^q); ∀ᶠ i in atTop, ∀ N'≥ N i,∀ k, b*(Lambda C.path.levels i)^e * ratioR C.S N' i θ ≤ (regulatorRun C N' k i)^d:= by
   intro N; filter_upwards [payroll_s C.path.levels hG _ hp θ hw e b d hb] with i hi n hn k; have h:i≤n:= (show i≤N i from Nat.le_add_right ..).trans hn
   let l:=Lambda C.path.levels i; have hl:0<l:= zero_lt_one.trans_le (lambda_large C.path.levels i); have he: ratioR C.S n i θ ≤ ratioR C.S (N i) i θ:=by
       unfold ratioR; apply Real.rpow_le_rpow (div_nonneg (Schedule.a_pos ..).le (Schedule.a_pos ..).le) _ hw.le;exact div_le_div_of_nonneg_right ((Schedule.strictAnti _).antitone hn) (Schedule.a_pos ..).le
   apply (le_trans (mul_le_mul_of_nonneg_left he (mul_nonneg hb (pow_nonneg hl.le _))) hi).trans; rw [show (-(↑d * Lambda C.path.levels i))= ↑d* (-l) from (by ring), Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.exp_pos _).le (hatted _ p _ _ _ h) _
end YM.FormalBulk08.First
