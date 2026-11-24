import YM.Integration.WilsonReflectedPublicStationFare

/-! The original weak measuring column's pre-expense has a fixed
coupling-power price at its own physical station. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicStationPrice
open GapsContact GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson
open Labels Source Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Matrix.Norms.Frobenius Classical
variable {G:Gauge} (C:Family G)
local notation "A!" => C.path.levels
local notation "β!" => C.path.levels.clock.hatBeta
local notation "P!" => C.path.levels.clock.monitor

theorem original (hG:G.Simple)(d:ℕ):∃K:ℝ,∃power:ℕ,1≤K ∧
    ∀ᶠ j:ℕ in atTop, ∀u:ℝ,u≤Perch.y (β! j) → preExpense C d j u≤K*(β! j)^power:=by
   let F':Labels.Frame G d:=C.labels.level d;let s := ∑ i : F'.Index, ((F'.grades i).1+(F'.grades i).2)
   let c:ℝ:=2^s; let b:ℝ:= 2*(Fintype.card F'.Index)*c
   refine ⟨max 1 b, s, le_max_left .., ?_⟩
   filter_upwards [pastTilt A! hG,monitor_upper A! hG] with j hQ hA
   intro u hu
   let x:= β! j; let B:= mag (A!) u j; have hx:1<x:= (A!).fits.delayed _
   have h : B ≤ x:= le_trans (tiltP (C:=C) _ hu) hQ
   have hv:0≤B:= (mag_pos ..).le
   let z:= 2*(P! j); change 2*(∑ i:F'.Index, ‖z^(F'.grades i).2*B^(F'.grades i).1‖)≤_*x^s
   have hp:0 ≤ z:=mul_nonneg zero_le_two (Real.exp_pos _).le
   have h₁(i:F'.Index) := Finset.single_le_sum (f:=fun i:F'.Index=>(F'.grades i).1+(F'.grades i).2) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
   let A(i:F'.Index):=(F'.grades i).1; let D(i:F'.Index):=(F'.grades i).2; have hh(i:F'.Index):A i+D i≤ s:= h₁ i
   have hu:z≤2*x:= mul_le_mul_of_nonneg_left hA zero_le_two
   have hc(i:F'.Index): ‖z^D i*B^A i‖ ≤ c*x^s:=by
      rw [Real.norm_of_nonneg (by positivity)]; refine (mul_le_mul (pow_le_pow_left₀ hp hu _) (pow_le_pow_left₀ hv h _) (by positivity) (by positivity)).trans ?_
      rw [mul_pow, mul_assoc, ← pow_add]; refine mul_le_mul (pow_le_pow_right₀ one_le_two (by linarith only [hh i])) (pow_le_pow_right₀ hx.le (by linarith only [hh i])) (pow_nonneg (zero_le_one.trans hx.le) _) (show 0≤c by unfold c; positivity)
   apply le_trans (b:=2*(∑ _i : F'.Index,c*x^s)) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> hc i)) zero_le_two); apply le_trans (b:=b*x^s) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)); simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold b; exact Eq.le (by ring)


end YM.Integration.WilsonReflectedPublicStationPrice
end
