import YM.QuadraticLocal.Close
import YM.QuadraticLocal.Class.Venture
/-!
# Close-teaching cost calendar
 Per-model radius fixed by user and repaid; the temporary shrink is just
 at the level of budgeting inside the analytic Semester. Powers here are for
 actual number of slots per monomial, not independent of it. Use close
 with any stipulated constants in manuscript, including q=ordinary 1 bound.
 `m` *below* `b`, report height (beta for these charges) at top b of evaluation,
 even if cutoff N≫b.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
open PaceR
open AllOrder.Catch
variable {G : Gauge}
variable (R:Run G)
variable (g:G.Simple)
variable {i k n m b:ℕ} {Q ε t :ℝ}
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "A"=> R.alloy.B.a
variable (U:Syl.School k)
-- none
local notation "H!"=> roof R (i+1) b
local notation "H"=> roof R i b
local notation "V"=> roof R m b
abbrev rent (R:Run G)(m i b:ℕ) := (roof R i b/ roof R m b)^2
local notation "p" v:max=> (Sycamore.rent R m v b)
abbrev tol (U:Syl.School k)(ε:ℝ):ℝ:= Catch.graded (U.order+1)+ε
abbrev notice (b:ℕ) (U:Syl.School k) (ε:ℝ):= (Φ b)^( Sycamore.tol U ε )
abbrev bill (U:Syl.School k):ℕ:= U.pieces+6
abbrev life (R:Run G)(i b:ℕ)(U:Syl.School k)(ε:ℝ):ℝ:=(roof R i b)^ (Sycamore.bill U) *notice R b U ε
local notation "T0"=> life R i b U ε
local notation "T'"=> life R (i+1) b U ε
local notation "f"=> roof
lemma behalf : 0 < notice R b U ε:= Real.rpow_pos_of_pos (PaceR.positive ..) _
lemma advance : notice R b U ε ≤ life R i b U ε:= le_mul_of_one_le_left (behalf R U|>.le) (one_le_pow₀ (roof_ge ..))
lemma toll_real : 0 < life R i b U ε:= lt_of_lt_of_le (behalf R U) (advance R U)
lemma roof_longer (h:m≤ i)(he:i≤b): roof R i b ≤ roof R m b:= by
    induction h using Nat.decreasingInduction with
    | self=> exact le_rfl
    | of_succ n h ih => rw [PaceR.roof_step R (lt_of_lt_of_le h he)]; exact ih.trans (le_mul_of_one_le_left (zero_le_one.trans (roof_ge ..)) (budget_pos R))
lemma roof_small (hi:i<b): budgetR R i ≤ roof R i b:=by rw [roof_step R hi]; exact le_mul_of_one_le_right (zero_le_one.trans (budget_pos R)) (roof_ge ..)
lemma flows (hi:i<b): life R i b U ε=(budgetR R i)^( Sycamore.bill U )*life R (i+1) b U ε:=by unfold life; rw [PaceR.roof_step R hi,mul_pow,mul_assoc]
lemma rent_le (h:m≤ i)(he:i≤b): Sycamore.rent R m i b ≤ 1:=pow_le_one₀ (div_nonneg (zero_le_one.trans (roof_ge ..)) (zero_le_one.trans (roof_ge ..))) ((div_le_one (zero_lt_one.trans_le (roof_ge ..))).mpr (roof_longer R h he))
lemma rent_pos : 0 < Sycamore.rent R m i b:= pow_pos (div_pos (zero_lt_one.trans_le (roof_ge ..)) (zero_lt_one.trans_le (roof_ge ..))) _
lemma rent_end : Sycamore.rent R m b b = ((roof R m b)^2)⁻¹:= by unfold Sycamore.rent; rw [show roof R b b=1 by simp [roof], one_div, inv_pow]
lemma spool (hi:i<b): Sycamore.rent R m i b=(budgetR R i)^2*(p (i+1)):=by unfold Sycamore.rent; rw [PaceR.roof_step R hi,mul_div_assoc,mul_pow]
-- economic facts independent of close Customer. Need b powers.Work.Role.Year.
lemma allot (K X v E e:ℝ)(k:ℕ)(h:4 ≤ K)(he:0≤ E)(hz:0≤e)(hv:0≤v)(hp:e ≤ E)(ht:v ≤ E)
    (hX : X ≤8*K*( K⁻¹ *E + e+v)) {T P C:ℝ}(hT:0≤T)(hh : T ≤ K)(hP:P ≤ K)(hc:0≤C)(hC:C≤1): v*T*(P*C)+K^k*X≤K^(k+6)*E:= by
    have hK:0≤K:=by linarith
    have hs:1≤K:=by linarith
    have hw:0≤K^k:= pow_nonneg hK _; have ha:P*C≤K:= (mul_le_mul_of_nonneg_right hP hc).trans (mul_le_of_le_one_right hK hC)
    have hr:v*T*(P*C) ≤ E*K^2 := by
       apply le_trans (b:=v*T*K) (mul_le_mul_of_nonneg_left ha (mul_nonneg hv hT)); apply (mul_le_mul_of_nonneg_right (mul_le_mul ht hh hT he) hK).trans; rw [mul_assoc,pow_two]
    let n:=K^k; have hy: K⁻¹* E ≤ E:=mul_le_of_le_one_left he (inv_le_one_of_one_le₀ hs); have h' : X ≤ (K^4)*E:=by
       refine hX.trans (le_trans (b:= 8*K*(E+E+E)) (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hy hp) ht) (by positivity : 0≤8*K)) ?_); suffices ht:24*K≤K^4 by linarith only [mul_le_mul_of_nonneg_right ht he]; -- powers proof
       rw [show (4:ℕ)=3+1 from rfl, pow_succ]; exact mul_le_mul_of_nonneg_right (le_trans (by norm_num : (24:ℝ) ≤ 4^3) (pow_le_pow_left₀ (by norm_num) h _)) hK
    rw [pow_add]; refine (add_le_add hr (mul_le_mul_of_nonneg_left h' hw)).trans (le_trans (b:= 2*(K^k*(K^4*E))) ?_ ?_); · rw [two_mul]; apply add_le_add_left; rw [mul_comm E]; apply le_trans _ (le_mul_of_one_le_left (by positivity : 0 ≤ K^4*E) (one_le_pow₀ hs)); exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hs (by norm_num : 2 ≤ (4:ℕ))) he
    rw [show (6:ℕ)=2+4 from rfl,pow_add K 2]; have h'':2*(K^4) ≤ K^2*K^4:= mul_le_mul_of_nonneg_right ((show (2:ℝ) ≤ 4^2 by norm_num).trans (pow_le_pow_left₀ (by norm_num) h _)) (pow_nonneg hK _); nlinarith only [mul_le_mul_of_nonneg_right h'' (mul_nonneg hw he)]
end YM.QuadraticLocal.Advent.Sycamore
