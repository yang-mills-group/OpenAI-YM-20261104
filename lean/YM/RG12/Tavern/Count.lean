import YM.RG12.Tavern.Bouncer
/-! # Quantitative connector on this calibration for input/output frames in Weather
 Thermal supplies pointwise outputs through order 2 with loss of 1/2 coupling and arbitrary
 Geometry *monitor* multiplicative (or better)! Needs that remainder *in these report frames*,
 any auxiliary projections/rotations/comparisons/kσ costs must be paid into it; not after
 the forbidden IR-transport step. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Tavern
open Frames Alidade Function Filter Set Lattice RG Rail Real
open Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{h:ℕ}{t:ℕ→ℝ}
variable (Z:Levels G)
variable {V:Grade h→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)]
local notation "A!"=>Col V
variable {F:Type}[AddCommGroup F][Module ℂ F]
variable (P:Col V≃ₗ[ℂ]F)(f:ℝ→Gram.Square F)(q:ℕ→ℝ)
-- Written in paired separately specified POSITION scheme; normalization conversion is an
-- obligation. Doesn't require expansion down to the sparse stress direction or for all cutoff
-- lifts. Norms all on slot coordinates. Errors include conversion of WilsonX param, e.g. if
-- using regulatorRun vs g^ex, need to prove choice & costs (or supply alternate q with
-- Barred); coefficient-side law crucial. One possible strong interface for RG05–11.
-- Q needs only eventually *contiguous lit* k; no PT comparison within or across the holiday interval.
def Plank (t:ℕ→ℝ)(Q:Wheel V)(lit:ℕ→Prop)(o:ℕ) : Prop :=
    ∀ᶠ k:ℕ in atTop, lit k→lit (k+1)→
       let ε:=q k;let u:=t k / t (k+1)
       let R:=Z.clock.monitor k ^o * (ε^2*Real.sqrt ε)
       ∃ (W : Col V≃ₗ[ℂ] F), formative W P ∧ ∀ x:A!,
        let e :=(f (t k)).eval (W (Frames.dilate u x))
        let l :=(f (t (k+1))).eval (W x)
        |l-Alidade.axis Q.C ε x| ≤ R*‖x‖^2 ∧ |e-Alidade.axis (Q.X u) ε x| ≤ R*‖x‖^2
variable {Z q P f}
variable {l:ℕ→ℝ}{Q:Wheel V}{K:ℝ}{lit:ℕ→Prop}{b:ℝ}{o:ℕ}{N:ℕ}
variable (hG:G.Simple)(hQ:Weather Q K)(hχ:Barred (Z:=C.path.levels) q b)
set_option quotPrecheck false
local notation "α"=> C.path.levels
local notation:max "χ(i" i ")"=> C.path.levels.clock.hatBeta i
local notation "μ"=> C.path.levels.clock.monitor
local notation "clk"=>epoch C.path.levels
include hχ hG
variable {γ:ℝ}
-- finance universal L response for relative price (abstract of Gram). order 5/2 tolerance bought
lemma penny (o:ℕ)(A K:ℝ)(hA:0 ≤ A) : let w(k):=Alidade.slice C.path.levels k
      let z(k:ℕ):=(2*Real.sqrt (q k)*μ k^o+A*w k)*q k^2
      ∃ p:ℕ, ∀ᶠ k:ℕ in atTop, let r:=clk (k+1) / clk k-1
                          (2*K*z k ≤ p*r ∧ (p:ℝ)*r ≤ 1/2):=by
   intro w z; let u:=abs K
   let T (k:ℕ):=2*Real.sqrt (q k)*μ k^o
   have he:=allowances hG hχ o; let x:= Gauge.slopeConstant G
   have hxx:0<x:=Gauge.slopeConstant_pos hG
   let c:=(1+A)*b*(2/x)
   obtain ⟨p,hp⟩:=exists_nat_gt (2*|K| *c)
   have hh:=he.eventually (ge_mem_nhds (show 0 < Real.log 3/2 by linarith only [arc3]))
   let ρ(k):= clk (k+1)/clk k-1
   have hY:Tendsto (fun k=> (p:ℝ)*ρ k) atTop (𝓝 0):=by simpa only [mul_zero] using! (history_rule (α) hG).const_mul (p:ℝ)
   refine ⟨p,?_⟩
   filter_upwards [hh,hY.eventually (ge_mem_nhds (show 0 < (1/2:ℝ) by norm_num)),entrance (α) hG] with k hk hk' hε r
   let i:=w k
   refine ⟨?_,hk'⟩
   have hz:0 ≤ T k:= mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (pow_nonneg (zero_le_one.trans (monitor_big ..)) _)
   have hu:= slice_first (α) k; have hw:0 < i:=arc3.trans_le hu
   have hv:T k ≤ i:=by unfold T i; dsimp only [w]; linarith only [hk,hu]
   have hP:0 ≤ r:=by unfold r; exact sub_nonneg.mpr (epoch_unit (α) k.le_succ)
   have hB:0 < b:= Barred.affords hχ
   let B:=Real.log 3*clk k; have hBB:0 < B:= mul_pos arc3 (zero_lt_one.trans_le (begun (α) k))
   have hiB: r=i/B:=by unfold r; rw [surges];simp only [add_sub_cancel_left];rfl
   have hf: B≤ (2/x) * χ(i k):= (div_le_iff₀ (year (α) k)).mp hε
   have hfQ: q k^2 * B ≤ b*(2/x) :=by
      refine (mul_le_mul_of_nonneg_left hf (sq_nonneg _)).trans ?_
      exact (mul_left_comm _ _ _).le.trans (by nlinarith only [mul_le_mul_of_nonneg_right (hχ.meters k) (by positivity : (0:ℝ) ≤ 2/x)])
   have hz0: z k ≤ c*r:=by
      change (T k+A*i)*q k^2 ≤_
      rw [hiB,← mul_div_assoc,le_div_iff₀ hBB]; unfold c
      nlinarith only [mul_le_mul_of_nonneg_right hfQ (show 0 ≤ i*(1+A) by positivity), mul_le_mul_of_nonneg_right hv (show 0 ≤ q k^2*B by positivity)]
   have hz':0 ≤ z k:= mul_nonneg (add_nonneg hz (mul_nonneg hA hw.le)) (sq_nonneg _)
   exact (mul_le_mul (show 2*K ≤ 2*|K| from by grw [← le_abs_self K]) hz0 hz' (by positivity)).trans (by have hi:= mul_le_mul_of_nonneg_right hp.le hP; linarith)

include hQ
lemma pennies (n:ℕ): ∀ᶠ k:ℕ in atTop, let y:=q k;let e:= Real.sqrt y* μ k^n
       K*y+K*y^2+e*y^2 ≤ (2*K)⁻¹:=by
   obtain ⟨h⟩:=hQ.prices
   have he1:=allowances hG hχ 0; simp only [pow_zero,mul_one] at he1
   have he : Tendsto q atTop (𝓝 0):=by
      have ht:= he1.pow 2; simp_rw [Real.sq_sqrt (hχ.positive _).le] at ht; simpa only [zero_pow (by norm_num:2≠0)] using! ht
   have hB : Tendsto (fun k=>K*q k+K*q k^2+(Real.sqrt (q k)*μ k^n)*q k^2) atTop (𝓝 0):=by
      simpa only [zero_pow (by norm_num:2≠0),mul_zero,add_zero] using! ((he.const_mul K).add ((he.pow 2).const_mul K)).add ((allowances hG hχ n).mul (he.pow 2))
   have ht:=h.hex; exact hB.eventually (ge_mem_nhds (show 0<(2*K)⁻¹ by positivity [zero_lt_one.trans_le ht]))
end YM.RG12.Tavern
