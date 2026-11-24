import YM.GapsContact.Travel.Join
import YM.GapsContact.Dusk.Treasury
import YM.TraceExtension.Terrace.Stanza

/-!
# One-step cluster-to-support pricing (final factor in post position)

Basin and ship gaps include price in terms of reference hatBeta. So can enter even
if full Wightman zoom radius fixes coupling and scales before pricing. Does not solve
quotient estimates or growth polylog of engineering's fixed reference.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Dusk
open Function Filter Set Lattice RG RG.Supply Wilson Push.PriceCompiler Push.GridApprox Vac Stock
open Trace.Terrace MergeProof Accent
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {A:Levels G} (C:Family G) (hg:G.Simple)
set_option quotPrecheck false
local notation "P"=> C.path.levels
local notation "β"=> C.path.levels.clock.hatBeta
variable (hf: Feasible C.path.levels) (ht:PostT C.path.levels) (L:Tabs C.path.levels)

private lemma across (S:Schedule){i j:ℕ}(he:i ≤ j) : (2:ℝ)^(j-i) ≤ S.a i/S.a j:=by
   induction j,he using Nat.le_induction with
   | base=> simp only [Nat.sub_self,pow_zero,div_self (S.a_pos i).ne',le_refl]
   | succ j he ih=>
      rw [show j+1-i=j-i+1 by omega,pow_succ', S.a_step];
      refine le_trans (mul_le_mul (show 2≤((S.block j).val:ℝ) from by exact_mod_cast (le_trans (by norm_num) (S.block_large j) : 2 ≤ (S.block j).val)) ih (by positivity) (by positivity)) (by have hx:= S.a_pos j; have he:0 < ((S.block j).val:ℝ):= (by exact_mod_cast (S.block j).property); exact Eq.le (by field_simp))

private lemma dell {a:ℝ} (ha:0<a):∀ᶠ x:ℝ in atTop,Real.log x ^ 2 ≤ a*x:= by
   filter_upwards [Real.isLittleO_pow_log_id_atTop (n:=2)|>.bound ha,eventually_ge_atTop (1:ℝ)] with x hx ht; simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log x)), id_eq,abs_of_nonneg (zero_le_one.trans ht)] using! hx
lemma end_nn (J m:ℕ):0<endpointT C J m:= div_pos (Real.exp_pos _) (pace_pos ..)
local notation "X" => basin P L
include hg ht hf
lemma yield_ticket : ∃ V:ℕ,∀ᶠ i:ℕ in atTop, endpointT C i (X i) ≤ β i ^ V:= by
   let l₂:=Real.log 2; let q:=lrate (P) hg; have hr:0 < l₂ := Real.log_pos (by norm_num)
   obtain ⟨V,hV⟩:= exists_nat_gt (6+customs G); refine ⟨V,?_⟩; let L(i):= gate (β i)
   filter_upwards [q.eventually_ge_atTop 100, Bgap (P) hg ht ‹_›, open_budget P hg ht ‹_›, bond (P) hg ht, treasury_stage P hg, q.eventually (dell (show 0 < l₂/500 from by positivity)),(Real.tendsto_log_atTop.comp q).eventually_ge_atTop l₂] with i hi hb hx hv ht hd hs
   let m:= X i; let k:= summit (P) i; let x:= L i; let y:= L m
   have ha:x ≤ y:=lypos P hg (unwinds ..)
   have he:y ≤ 2*x:= (lypos P hg (show m ≤ k from hx.le)).trans hv.2.1; have hx :100 ≤ x:=hi; have hX:0<x:=(by linarith); have hy:0<y:=lt_of_lt_of_le hX ha;
   have hβ:0 < β i:=zero_lt_one.trans ((P).fits.delayed _); have hβ':0 < β m:=zero_lt_one.trans ((P).fits.delayed _); have hh:0<paceFactor C.path m i:=pace_pos ..
   let Y:=Real.log x; let N:=m-i; have hu:l₂≤Y:=hs; have hZ:= Real.log_le_log (y:=x^6) (pow_pos zero_lt_two N) ((across C.S (unwinds ..)).trans hb.1)
   simp only [Real.log_pow,Nat.cast_ofNat] at hZ; change ↑N*l₂ ≤ 6*Y at hZ; have hD: Y^2 ≤ l₂/500*x:=hd
   have hU: Real.log y ≤ 2*Y:=by
      apply (Real.log_le_log hy he).trans; rw [Real.log_mul (by norm_num) hX.ne']; change l₂+Y ≤ _; linarith
   apply (Real.log_le_log_iff (end_nn ..) (pow_pos hβ _)).1; unfold endpointT; rw [Real.log_div (Real.exp_pos _).ne' hh.ne',Real.log_exp,Real.log_pow,show paceFactor C.path _ i = coupon (β m)*aBrake (β m)^N from rfl,Real.log_mul (coupon_nn hβ').ne' (by exact (pow_pos (brake_nn ((P).fits.delayed _)) N).ne'),Real.log_pow,aBrake,Real.log_inv,Real.log_pow,coupon,Real.log_rpow hβ']; change treasury P i+5 -((- (2:ℝ))*y + (N:ℝ)*(-((40:ℕ)*Real.log y))) ≤ V*x
   have h : (N:ℝ)*Real.log y ≤ (12/l₂)*Y^2 :=by
      apply (mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg N)).trans; refine le_trans (mul_le_mul_of_nonneg_right ((le_div_iff₀ hr).2 hZ) (by linarith only [hu,hr])) (le_of_eq ?_); field_simp; ring
   have hJ : (40:ℝ)*((12/l₂)*Y^2) ≤ x:=by
      refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD (show 0≤12/l₂ by positivity)) (by norm_num)) ?_; field_simp; nlinarith only [mul_pos hX hr]
   have hT: treasury P i ≤ customs G*x:= ht.trans (hf i); push_cast; linarith only [hT,h,hJ,hV,hx,he,mul_lt_mul_of_pos_right hV hX]
end YM.GapsContact.Dusk
