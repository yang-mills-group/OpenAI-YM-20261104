import YM.QuadraticLocal.Board
/-!
# Making room for full physical comparison on actual close intervals

Talk deals with short log geometry (close := any fixed setup multiple times powers of
loglog ˆβ top; delay independent of period). A single complete binding supplies infinitely many
local comparisons.Warp actual couplings through Bloch orientation, monotone hats, appearances.
YARD (initiation): every short terminal or ancestor interval asked, even for allowed `Π Epoch`
activation at top and a subwindow. Conversion exponential radii ≤ ˆβ^ε even at all stages
varying up to their prescribed k -- **NOT uniform** in marker count at restore!

No assertion here about separation upper fine propagation: focuses on the analytic close recursion.
Use deterministic close arithmetic also at subwindows before reset param. Must still prove
comparison & next admission at close by patchwork; closeness assumption itself can be used
independently of prescription.J.Crest. For longer logTheta windows ask other estimates. We retain
orientation log log, not fixed number of steps. Every hG uses explicit Angle.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G : Gauge}
variable (R:Run G)
variable (g:G.Simple)
variable {i n m b:ℕ} {Q:ℝ}
namespace PaceR
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "Λ"=> fun i=> (2+Real.log (Φ i):ℝ)
local notation "C"=> R.alloy.B.a
local notation "ω"=>fun i=> Real.log (Λ i)
local notation "S"=> R.family.S
abbrev zeta (x:ℝ): ℝ:=1+ max 0 (Real.log (Real.log x))
local notation "K"=> fun i=> (Beaming.spray (Φ i))
lemma positive (i:ℕ): 0 < Φ i:= zero_lt_one.trans ((C).fits.delayed i)
lemma positive_log (i:ℕ) : 0 < Real.log (Φ i):= Real.log_pos ((C).fits.delayed i)
lemma positive_clock (i:ℕ) : 0 < ω i:= Real.log_pos (by change 1<2+Real.log (Φ i); linarith only [positive_log R i])
lemma logC (i:ℕ): Real.log (Real.log (Φ i)) ≤ ω i:= Real.log_le_log (positive_log ..) (by change Real.log _ ≤ 2+_; linarith) -- maybe coercion
lemma clock_bound (i:ℕ) : zeta (Φ i) ≤ 1+ω i:=add_le_add_right (max_le (positive_clock _ _).le (logC _ _)) _
include g
lemma clock_mono (h:i≤b) : Φ i ≤ Φ b:= WilsonStartup.Timing.hat_mono C (Gauge.slopeConstant_pos g).le h
lemma tempo_m (h:i≤b): zeta (Φ i) ≤ zeta (Φ b):= by
    unfold zeta; exact add_le_add_right (max_le_max le_rfl (Real.log_le_log (positive_log R i) (Real.log_le_log (positive R i) (clock_mono R g h)))) _
lemma lawn (h:i≤b): roof R i b ≤ (Beaming.spray (Φ b))^(b-i):=by
    refine le_trans (b:=∏ _∈ Finset.Ico i b,K b) (prod_le_prod (fun i _=>zero_le_one.trans (budget_pos R)) (fun j hj=>?_)) (by simp)
    apply le_trans (a:=budgetR R j) (b:=Beaming.spray (Φ (j+1))) (min_le_left ..); exact Real.exp_monotone (pow_le_pow_left₀ (show 0≤zeta (Φ (j+1)) from add_nonneg zero_le_one (le_max_left ..)) (tempo_m R g (mem_Ico.mp hj).2) _)
def Close (R : Run G)(q:ℕ)(Q:ℝ)(m b:ℕ):=(R.family.S.scale b-R.family.S.scale m) ≤ Q*Real.log (2 + Real.log (R.alloy.B.a.clock.hatBeta b)) ^ q
omit g in
lemma distance (h:m≤b) : ((b-m:ℕ):ℝ)* Real.log 3 ≤ (S).scale b-(S).scale m:=by
   induction b,h using Nat.le_induction with
   | base=>simp
   | succ b h ih=>
      rw [(S).scale_succ,Nat.succ_sub h]; push_cast
      have he : Real.log 3 ≤ Real.log ((S).block b).val:= Real.log_le_log (by norm_num) (show (3:ℝ) ≤ ((S).block b).val from by exact_mod_cast (S).block_large b)
      linarith
private lemma hat_rate : Tendsto Φ atTop atTop:=
    tendsto_const_nhds.add_atTop ( (C).S.divergent.const_mul_atTop (Gauge.slopeConstant_pos g))
-- parse
/-- uniform for varying constants fixed degree. Unit etc unused. -/
lemma scarce (M ε:ℝ)(he:0<ε)(q:ℕ) : ∀ᶠ b:ℕ in atTop, M*(ω b)^q ≤ ε* Real.log (Φ b):=by
    have hu: Tendsto (fun b=> 2+Real.log (Φ b)) atTop atTop:= tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp (hat_rate R g)); let hh:= (Real.isLittleO_pow_log_id_atTop (n:=q)).const_mul_left M
    have hx:= hu.eventually (hh.def (half_pos he))
    filter_upwards [hx,(Real.tendsto_log_atTop.comp (hat_rate R g)).eventually_ge_atTop 2] with b hb hz
    let z:= Real.log (Φ b); have hm : 2≤z:= hz; change ‖M*(ω b)^q‖ ≤ ε/2*‖(2+z:ℝ)‖ at hb; rw [Real.norm_of_nonneg (show 0≤2+z by linarith)] at hb; exact (Real.le_norm_self _).trans (hb.trans (by change ε/2 * _ ≤ ε*z; nlinarith))
lemma gives (q k:ℕ)(Q:ℝ) (hp:0 ≤ Q)(ε:ℝ)(he:0<ε) : ∀ᶠ b:ℕ in atTop, ∀ (m i:ℕ),m≤ i→i≤b→Close R q Q m b→(roof R i b)^k ≤ (Φ b)^ε := by
   let A:= Real.log 3; have hA:0<A:=Real.log_pos (by norm_num); let r:=8*(Q/A)* (k:ℝ)
   let ht:= ((Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp (hat_rate R g)))): Tendsto (fun i=> Real.log (2+Real.log (Φ i))) atTop atTop)
   filter_upwards [ht.eventually_ge_atTop 1, scarce R g r ε he (q+3)] with b hb h m i hi hj hB
   let z:= Real.log (2+ Real.log (Φ b)); let y:= Beaming.spray (Φ b); have hx : 1 ≤ z:= hb; have hm : (Φ b)>0:= positive R b
   have hp :( ((b-i:ℕ):ℝ))*A ≤ Q*z^q:= (le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega : b-i≤b-m)) hA.le) (distance R (hi.trans hj))).trans hB
   refine le_trans (pow_le_pow_left₀ (zero_le_one.trans (roof_ge R i b)) (lawn R g hj) _) ((Real.log_le_log_iff (show 0< (y^(b-i))^k from pow_pos (pow_pos (Real.exp_pos _) _) _) (Real.rpow_pos_of_pos hm _)).mp ?_)
   rw [Real.log_pow,Real.log_pow]; change k*( ( (b-i:ℕ):ℝ) * Real.log y)≤ Real.log _; rw [show Real.log y= zeta (Φ b)^3 from Real.log_exp _, Real.log_rpow hm]
   have hh:((b-i:ℕ):ℝ) ≤ Q/A*z^q:= by rw [div_mul_eq_mul_div]; exact (le_div_iff₀ hA).mpr hp
   have hg: zeta (Φ b) ≤ 2*z:= (clock_bound R b).trans (by change 1+z≤_; linarith)
   refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul hh (pow_le_pow_left₀ (show 0≤zeta (Φ b) from add_nonneg zero_le_one (le_max_left ..)) hg 3) (pow_nonneg (show 0≤zeta (Φ b) from add_nonneg zero_le_one (le_max_left ..)) _) ( (Nat.cast_nonneg _).trans hh)) (Nat.cast_nonneg k)) (?_: (k:ℝ)*(Q/A*z^q *(2*z)^3) ≤ _); exact le_trans (le_of_eq (show _ = r*(ω b)^(q+3) from (by unfold r z; ring))) h
/-- Close the requested interval from the terminal fine end. Budget heights uniform across requests satisfying same window. -/
lemma covers_hat (q:ℕ)(Q:ℝ): ∀ᶠ b:ℕ in atTop,∀ i m:ℕ,m≤ i→i≤b→Close R q Q m b→Φ b/2 ≤ Φ i:=by
   filter_upwards [scarce R g (G.slopeConstant * Q) (1/2) (by norm_num) q] with b h i m hi hj hz
   apply le_trans _ (clock_mono R g hi); suffices hx : Φ b-Φ m ≤ Φ b/2 by linarith
   have hx : Φ b-Φ m=G.slopeConstant*((S).scale b-(S).scale m):= by unfold Calendar.hatBeta; change _+_*(S).scale b-((C).clock.bar +_* (S).scale m)=_; ring
   rw [hx]; change (G.slopeConstant*Q)* (ω b)^q ≤ _ at h; rw [mul_assoc] at h; apply le_trans (le_trans (mul_le_mul_of_nonneg_left hz (Gauge.slopeConstant_pos g).le) h); linarith only [Real.log_le_self (positive R b|>.le)]
lemma on_tail (q:ℕ)(Q:ℝ)(j:ℕ) : ∀ᶠ b:ℕ in atTop,∀ m≤b,Close R q Q m b → j ≤ (R.family.path.levels.clock.J m):=by
    obtain ⟨k,hk⟩:= ((C).fits.deep.eventually_ge_atTop j).exists
    filter_upwards [covers_hat R g q Q, (hat_rate R g).eventually_gt_atTop (2 * Φ k)] with b h hh m hm hp
    have hv : k ≤ m:= by
       by_contra! hi; linarith only [clock_mono R g hi.le,h m m le_rfl hm hp,hh]
    exact le_trans hk ((C).fits.mono hv)
end PaceR
end YM.QuadraticLocal.Advent
