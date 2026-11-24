import YM.QuadraticLocal.Class.Clockwork
import Mathlib.Analysis.Complex.ExponentialBounds
/-! # The marker envelope is not e^ε only: close kernel exponential-polynomial costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open AllOrder AllOrder.Burn MintClock
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Asymptotics
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open Input Org Wilson ThroughLaunch PriceCompiler
open Legato Legato.VowsR PaceR Boot Eon
variable {G:Gauge} (R:Run G)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
variable {m i u k b:ℕ}
local notation "A"=> R.alloy.B.a
local notation "S"=> R.family.S
set_option quotPrecheck false
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
open Spill.Walking
namespace Shuttle
variable {φ:ℕ→ℕ} (θ : Spill.Walking.Reach G D R.alloy.delay φ)
local notation "K_"=> R.family.path.levels.clock.J i
local notation "J_"=> R.family.path.levels.clock.J (i+1)
variable (g:G.Simple)
include g
set_option quotPrecheck false
local notation "w"=> ( whirl ( Φ b ) )
local notation "Zy"=> ( zeta (Φ b ) )
local notation "α"=> Real.log ( Real.log (Φ b) )
open Real (exp log)
omit g
lemma compar : w ≤ Zy+(Real.log 4):=by
   let y:= Real.log (Φ b); have hy : 0<y:= PaceR.positive_log R b; unfold whirl; change Real.log (2+y) ≤ _
   by_cases hh: y≤ 1
   · have ht : 2+y≤4:= (by linarith only [hh]); exact (Real.log_le_log (add_pos zero_lt_two hy) ht).trans (le_add_of_nonneg_left (add_nonneg zero_le_one (le_max_left ..)))
   have he : 2+y ≤ 4*y:= (by linarith only [hh]); refine (Real.log_le_log (add_pos zero_lt_two hy) he).trans ?_; rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hy.ne']; unfold zeta; linarith only [( le_max_right 0 ( Real.log y ) )]
include g
-- stronger than `≤ Φ^τ` registration's θ in `Printed.market .budget`, for every permitted Φ(b) close radius. True exponent ≤ C_k ζ^(q+3) from Π.E.weight ledger. Re-expression may store extra B metadata; no semantic costs outside tested arity.
-- upper bound all along close corridors. After Actor.Meta.Resource.Region.S.Pupil.My.Path memory.
lemma budget_lit (q k:ℕ) (Q:ℝ) (h : m≤ i) (he: i≤b)(hC:PaceR.Close R q Q m b) (hp:0≤Q) : ( PaceR.roof R i b )^k ≤ Real.exp ( (k:ℝ) * ( Q*(Zy+Real.log 4)^q/Real.log 3 ) * Zy^3 ):=by
   let a:= Real.log 3; have ha:0<a:= Real.log_pos (by norm_num)
   let gx := Zy; have hx:1≤ gx:=le_add_of_nonneg_right (le_max_left ..)
   let c:=(Beaming.spray (Φ b)); have hc: c=Real.exp (gx^3):=rfl
   have h0 : (0:ℝ) ≤ w:= PaceR.positive_clock R b|>.le
   have h1 : ((b-i:ℕ):ℝ) ≤ Q*(Zy+Real.log 4)^q/Real.log 3:= by
      apply (le_div_iff₀ ha).mpr
      calc
        _ ≤ ((b-m:ℕ):ℝ)*a := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) ha.le
        _ ≤ ( Q * w^q ) := (distance R (h.trans he)).trans hC
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (compar R) _) hp
   apply le_trans ( pow_le_pow_left₀ (zero_le_one.trans ( roof_ge R i b )) (lawn R g he) k )
   change (c^_)^_ ≤ _
   rw [hc, ← Real.exp_nat_mul,← Real.exp_nat_mul]; apply Real.exp_monotone
   rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (pow_nonneg (zero_le_one.trans hx) _)) (Nat.cast_nonneg _)
end Shuttle
end YM.QuadraticLocal.Advent.Sycamore
