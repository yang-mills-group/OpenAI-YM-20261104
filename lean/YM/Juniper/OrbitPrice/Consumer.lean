import YM.Juniper.OrbitPrice.Carry
import YM.Juniper.Provider.Context
/-!
 # Local one unmarked representation consumers at actual g, frozen UV family

 Carry is in hatβ units. Here instantiate on the actual RegulRun of this C,
 not C.chart, not s := log(a_m), not perturbative position coupling nor
 ratio w.r.t. the calibrated field threshold and not actual beta from another
 possibly compatible rep. Also keep the Boot comparison hypotheses VISIBLE;
 they own nonuniform and order budgets together. Pulse exported separately.
 These comparisons are on this ACTUAL density representation & kernel. No
 assertion about `Boot` at a PT model or parameter independence needed of it!
 Need prove exact agreement and pay of the renderer orientation etc. Not yet
 the qpta/readout estimates. `Crests` for ANY b around bar true UV supply.
 This `Core` is b=0. No assertion for disconnected atlas branches. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Native
open UVExtension Function Filter Set Lattice Wilson RG Shoot Supply Pressure Precision
open Org PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open ThroughLaunch Roof Roost Input Progress.DirectedRecipe Time Camp Oriel
open Tabernacle Dales Guild Spire
open Pert.Asymptotics
open scoped Topology BigOperators InnerProductSpace Classical
variable {G : Gauge}

namespace Core
variable {hG : G.Simple} (C : Nursery G hG)
local notation "p" => C.A.B.a
local notation "S"=> C.S
local notation "f" => C.family
local notation "T" => C.family.path
variable (n m q r : ℕ)
lemma witness : (T).rep n m r=C.S.realBeat 0 n m r := rfl
lemma printed (_hi:r ≤ n): ((T).rep n m r).activities = Tabernacle.floor ((p).budget r) (genes C.X hG S n m 0 r|>.val):= rfl -- redundant hi linter

include hG
private lemma center : (((0:ℝ):ℂ))∈Camp.Broad C.A.B.a:= (by simp only [Complex.ofReal_zero]; exact Metric.mem_ball_self (Camp.flat_pos _))
local notation "t!" => regulatorRun f n m r
local notation "h!" => bill p
local notation "a"=> p -- parser
omit hG in
private lemma hb (u v:ℝ)(h:0<u)(hp : 0<v) (he:u/2 ≤ v)(hv:v ≤ 2*u):
     (Real.sqrt v)⁻¹ ≤ 2*(Real.sqrt u)⁻¹ ∧ (Real.sqrt u)⁻¹ ≤2*(Real.sqrt v)⁻¹:= by
     rw [← one_div (Real.sqrt v),← one_div (Real.sqrt u),mul_one_div,mul_one_div]
     have ha:= Real.sqrt_pos.mpr hp; have hz:= Real.sqrt_pos.mpr h; rw [div_le_div_iff₀ ha hz,div_le_div_iff₀ hz ha]
     have hy:= Real.sq_sqrt hp.le;have hb:= Real.sq_sqrt h.le; constructor <;> nlinarith
-- above hG & unused C?
private lemma hats (hr:r ≤ n) : let t:= regulatorRun C.family n m r; let u:= C.A.B.a.clock.hatCoupling r
    0<t ∧ t ≤ 2*u ∧ u ≤ 2*t := by
   intro t u; have hz:= ((S).ticking n m (center C)).prices r (Nat.zero_le _) hr|>.2
   let v:=(p).clock.hatBeta r; have hp: 1<v := (p).fits.delayed r
   let y:= (T).β n m r; have ht : v/2 ≤ y∧ y≤ 2*v := hz; have hV:0<v:= zero_lt_one.trans hp
   have he:0<y:= (half_pos hV).trans_le ht.1; exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr he), hb v y hV he ht.1 ht.2⟩
private lemma naturally (hr:r ≤ n)(D:ℝ)(h:0 ≤ D): bill (p) D r ≤ (2:ℝ)^D * regulatorRun f n m r ^ D :=
   (Real.rpow_le_rpow (sized_pos p r).le (hats C n m r hr|>.2.2) h).trans_eq (Real.mul_rpow (by norm_num) (hats C n m r hr).1.le)

variable (M:ℕ)(W U D:ℝ) (model : ∀ N m i:ℕ, (C.S.fits N m).Home i)
variable (boot:∀ N m, M ≤ N → Boot C.X hG C.S N m 0 M W D (model N m))
local notation "x!"=> genes C.X hG C.S
include boot
lemma success : 11/5 ≤ W ∧ 0 ≤ D ∧ ∀ i≥M, ∀ N≥i, ∀ m:ℕ, let θ:= (p).budget i
      (Tabernacle.floor θ (x! N m 0 i-model N m i).val).EBound θ
          (D/(1-soft)*(2^W)*(regulatorRun f N m i)^W):= by
   have hp: 0 ≤ D := (boot M 0 le_rfl).costs; have he: 11/5 ≤ W := (boot M 0 le_rfl).order
   refine ⟨he,hp,fun i hi N hn m=>?_⟩; intro θ
   have h:=boot N m (hi.trans hn); apply Time.E_rises ((carry C.X hG S N m 0 (center C) M W D (model N m) h i hn hi).1)
   rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (naturally C N m i hn W ((by norm_num : (0:ℝ) ≤ 11/5).trans he)) (div_nonneg hp (by norm_num [soft,rim]))

-- use perhaps relative budget with θ^2. Here maps to reset at actual g of input.
variable (P : ℕ→ℕ→ℕ→ℝ) -- for application, as evaluated from formal algorithm with actual calibration.
variable (hP:∀ N m i (h:i<N),M ≤ i → |pulsePass C.X hG C.S N m 0 i h (model N m (i+1)) - P N m i| ≤ U*bill C.A.B.a (W-11/5+4/25) (i+1))
include hP
lemma energized (_h:0 ≤ U) : 0 ≤ D ∧ ∀ i≥M,∀ N>i,∀ m, let r:= W-11/5+4/25
      |(T).β N m i - (T).β N m (i+1) - P N m i| ≤ ((D/(1-soft)+U)*(2:ℝ)^r) * regulatorRun C.family N m (i+1)^r:= by
    have hz: 0 ≤ D := (boot M 0 le_rfl).costs
    refine ⟨hz, fun i hi N hn m=>?_⟩; intro r; have h₀ : 0 ≤ r := by unfold r; linarith only [(boot N m (by omega)).order]
    apply le_trans (reset C.X hG S N m 0 (center C) M W D U (P N m) (model N m) (boot N m (by omega)) (hP N m) i hn hi)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (naturally C N m (i+1) hn r h₀) (add_nonneg (div_nonneg hz (by norm_num [soft,rim])) _h)
end Core
end YM.Juniper.Native
