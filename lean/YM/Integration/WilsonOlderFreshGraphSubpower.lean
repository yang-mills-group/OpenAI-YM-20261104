import YM.Integration.WilsonOlderFreshGraphNamedPost

/-! All source-dependent rent above the rooted norm grows by less than
every positive fixed power of the original forecast, uniformly in the top
cutoff, period and numerical ballot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphSubpower
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical

open Real WilsonOlderFreshGraphSubmit
variable {d Q:ℕ}
def mass (B:Fin (d+Q+1)→ℝ):ℝ:=
  ∑ e:Fin (Q+1),∑ r:Fin (d+e.val+1), B (r.castLE (by omega))
def degree (v:Fin (d+Q+1)→ℕ):ℕ:=∑r,v r

lemma smallRoof (B:Fin (d+Q+1)→ℝ) (v:Fin (d+Q+1)→ℕ) (b0:∀r,0≤B r)
    {x:ℝ} (healthy:1 ≤ log x):
    roof (d:=d) (Q:=Q) B v x ≤ mass (d:=d) (Q:=Q) B *(log x)^(degree v) := by
  have a0:0 ≤ ageZ x:=by change 0 ≤ 1+log (log x);linarith [Real.log_nonneg healthy]
  have a1:ageZ x ≤ log x:=by
    change 1+log (log x) ≤ log x
    linarith [Real.log_le_sub_one_of_pos (by linarith:0<log x)]
  have z (u:Fin (d+Q+1)):ageZ x^(v u) ≤ (log x)^degree v:=
    (pow_le_pow_left₀ a0 a1 _).trans (pow_le_pow_right₀ healthy
      (Finset.single_le_sum (f:=v) (fun _ _=>Nat.zero_le _) (Finset.mem_univ u)))
  unfold roof mass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e _
  unfold WilsonOlderFreshGraphSubmit.charge
  rw [abs_of_nonneg (Finset.sum_nonneg (fun r _=>mul_nonneg (b0 _) (pow_nonneg a0 _))),Finset.sum_mul]
  exact Finset.sum_le_sum (fun r _=>mul_le_mul_of_nonneg_left (z _) (b0 _))

theorem price (B:Fin (d+Q+1)→ℝ) (v:Fin (d+Q+1)→ℕ) (b0:∀r,0≤B r) {δ:ℝ} (positive:0<δ):
    ∀ᶠ x:ℝ in atTop,∀ M:ℝ, 0 ≤ M →
      sqrt (log x)*(1+roof (d:=d) (Q:=Q) B v x*M) ≤ x^δ*(1+M):= by
  let C:=mass (d:=d) (Q:=Q) B
  let l:=degree v
  have c0:0 ≤ C:=Finset.sum_nonneg (fun e _=>Finset.sum_nonneg (fun r _=>b0 _))
  have C0:0<1+C:=by linarith
  have small:=(isLittleO_log_rpow_rpow_atTop ((l+1:ℕ):ℝ) positive).def (inv_pos.mpr C0)
  filter_upwards [small,tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with x hx one low
  intro M hm
  have b:0 ≤ log x:=by linarith
  have lb:1 ≤ log x^l:=one_le_pow₀ one
  have sq:sqrt (log x) ≤ log x:=by
    refine (sqrt_le_iff).2 ⟨b,?_⟩
    nlinarith
  have hroof:=smallRoof B v b0 one
  have plain:0 ≤ roof (d:=d) (Q:=Q) B v x:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  change ‖(log x)^((l+1:ℕ):ℝ)‖ ≤ (1+C)⁻¹*‖x^δ‖ at hx
  rw [Real.rpow_natCast,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg b _),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  have win:(1+C)*(log x)^(l+1) ≤ x^δ:=by
    have how:=mul_le_mul_of_nonneg_left hx C0.le
    simpa [← mul_assoc,mul_inv_cancel₀ C0.ne'] using how
  have start:sqrt (log x)*(1+roof B v x) ≤ (1+C)*(log x)^(l+1):=calc
    sqrt (log x)*(1+roof B v x) ≤ log x*((1+C)*(log x)^l):=by
      apply mul_le_mul sq _ (by positivity) b
      change roof B v x ≤ C*(log x)^l at hroof
      nlinarith
    _ = _:=by rw [pow_succ];ring
  calc
    sqrt (log x)*(1+roof B v x*M) ≤ (sqrt (log x)*(1+roof B v x))*(1+M):=by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
      nlinarith
    _ ≤ x^δ*(1+M):=mul_le_mul_of_nonneg_right (start.trans win) (by positivity)

theorem on_run {G:Gauge} (R:Run G) (simple:G.Simple)
    (B:Fin (d+Q+1)→ℝ) (v:Fin (d+Q+1)→ℕ) (b0:∀r,0≤B r) {δ:ℝ} (positive:0<δ):
    ∀ᶠ i:ℕ in atTop,∀ M:ℝ,0 ≤ M →
      let β:=R.alloy.B.a.clock.hatBeta i
      sqrt (log β)*(1+roof (d:=d) (Q:=Q) B v β*M) ≤ β^δ*(1+M):=by
  have growth:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  exact growth.eventually (price B v b0 positive)
end YM.Integration.WilsonOlderFreshGraphSubpower
end
