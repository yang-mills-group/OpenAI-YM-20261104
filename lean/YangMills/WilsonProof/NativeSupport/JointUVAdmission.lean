import YangMills.WilsonProof.NativeSupport.JointHistoryWallet
import YangMills.WilsonProof.NativeSupport.JointPrimitiveTests
import YangMills.WilsonProof.NativeSupport.JointForcedClock
import YangMills.WilsonProof.NativeSupport.FrozenCalendar

/-! Admission on every original inlet date. The source radius and the
campaign tariff are fixed before the reference truncation is chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}
theorem actual_band (R:Run G) (N per:ℕ) (heat:2 ≤ R.alloy.B.a.clock.hatBeta N):
    let x:ℝ:=height R N
    let g:=regulatorRun R.family N per N
    0<g ∧ g ≤ 1 ∧ x ≤ 4/g^2 ∧ g^2 ≤ 4/x := by
  intro x g
  let b:=R.alloy.B.a.clock.hatBeta N
  let B:=R.family.path.β N per N
  have lower:b/2 ≤ B:=(R.T.choice.represents N per N le_rfl).band.1
  have b2:2 ≤ b:=heat
  have B1:1 ≤ B:=by linarith only [lower,b2]
  have B0:=zero_lt_one.trans_le B1
  have ceiling:x ≤ 2*b:=by have hc:=Nat.ceil_lt_add_one (show 0 ≤ b by linarith);change (Nat.ceil b:ℝ) ≤ 2*b;linarith
  have x0:0 < x:=(show 0 < b by linarith).trans_le (Nat.le_ceil _)
  have gp:0 < g:=inv_pos.mpr (Real.sqrt_pos.mpr B0)
  have g1:g ≤ 1:=inv_le_one_of_one_le₀ (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt B1)
  have sq:g^2=B⁻¹:=by change (Real.sqrt B)⁻¹^2=B⁻¹;rw [inv_pow,Real.sq_sqrt B0.le]
  refine ⟨gp,g1,?_,?_⟩
  · rw [sq,div_inv_eq_mul];linarith only [ceiling,lower]
  · rw [sq,le_div_iff₀ x0,inv_mul_eq_div,div_le_iff₀ B0];linarith only [ceiling,lower]

theorem thermal_radius (d p:ℕ) {x g c:ℝ} (xp:0<x) (c0:0 ≤ c) (g0:0 ≤ g) (g1:g ≤ 1)
    (band:g^2 ≤ 4/x) (order:2*(2*d+1) ≤ p) (admit:2*c*4^(2*d+1) ≤ x) :
    2*(g^p*c) ≤ ((x^d)⁻¹)^2 := by
  have power:g^p ≤ (4/x)^(2*d+1) :=
    (pow_le_pow_of_le_one g0 g1 order).trans (by rw [pow_mul];exact pow_le_pow_left₀ (sq_nonneg _) band _)
  calc
    2*(g^p*c) ≤ 2*((4/x)^(2*d+1)*c) := by gcongr
    _ = (2*c*4^(2*d+1))/x^(2*d+1) := by rw [div_pow];ring
    _ ≤ x/x^(2*d+1) := div_le_div_of_nonneg_right admit (pow_nonneg xp.le _)
    _ = ((x^d)⁻¹)^2 := by rw [pow_succ,show 2*d=d*2 from Nat.mul_comm ..,pow_mul,inv_pow];field_simp

theorem budget_roof (R:Run G) (simple:G.Simple) {i N:ℕ} (upto:i ≤ N) :
    ((R.alloy.B.a.budget i).B:ℝ) ≤ 2*(height R N:ℝ)^2 := by
  let A:=R.alloy.B.a
  let x:=height R N
  have lb:Real.log (A.clock.hatBeta N) ≤ (x:ℝ):=by
    have v:=Real.log_le_sub_one_of_pos (zero_lt_one.trans (A.fits.delayed N))
    have top:=Nat.le_ceil (A.clock.hatBeta N)
    change _ ≤ (Nat.ceil (A.clock.hatBeta N):ℝ);linarith
  have lk:Real.log (A.clock.hatBeta i) ≤ x:=(Real.log_le_log (zero_lt_one.trans (A.fits.delayed i)) (monotone_hat A simple upto)).trans lb
  have sq:=pow_le_pow_left₀ (Real.log_nonneg (A.fits.delayed i).le) lk 2
  have h:(A.budget i).B ≤ 2*x^2:=by apply Nat.ceil_le.mpr;push_cast;linarith only [sq,sq_nonneg (x:ℝ)]
  exact_mod_cast h

theorem inlet_admission (R:Run G) (simple:G.Simple) (m W s ν:ℕ) (c:ℝ) (cp:1 ≤ c) :
    ∀ᶠ k:ℕ in atTop,∀ t N,k ≤ t → t ≤ N →
      R.family.S.scale N-R.family.S.scale t ≤ (W:ℝ)*Real.log (R.alloy.B.a.clock.hatBeta N) →
      let x:ℝ:=height R N
      let b:=priceDegree W s
      let d:=radiusDegree W s ν
      256 ≤ x ∧ 2*c ≤ x ∧ 64*((m:ℝ)+W+1) ≤ x ∧
        (∀ l,t ≤ l → l ≤ N → (R.alloy.B.a.clock.forcedAllowance l ≤ 1/x^b ∧
          Real.sqrt (R.alloy.B.a.clock.forcedAllowance l) ≤ 1)) ∧
        ∀ per p,2*(2*d+1) ≤ p →
          let g:=regulatorRun R.family N per N
          0<g ∧ g ≤ 1 ∧ x ≤ 4/g^2 ∧ 2*(g^p*c) ≤ ((x^d)⁻¹)^2 := by
  let b:=priceDegree W s
  let d:=radiusDegree W s ν
  let H:=max 256 (max (2*c) (max (64*((m:ℝ)+W+1)) (2*c*4^(2*d+1))))
  obtain ⟨cut,hot⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate R.alloy.B.a simple).eventually_ge_atTop H)
  filter_upwards [eventually_ge_atTop cut,inlet_forced_clock R simple W (2*b)] with k kt forced
  intro t N kl tn span x _ _
  have hb:H ≤ R.alloy.B.a.clock.hatBeta N:=hot N (kt.trans (kl.trans tn))
  have hx:H ≤ x:=hb.trans (Nat.le_ceil _)
  have hotN:256 ≤ R.alloy.B.a.clock.hatBeta N:=(le_max_left ..).trans hb
  have hotX:256 ≤ x:=(le_max_left ..).trans hx
  have mid: max (2*c) (max (64*((m:ℝ)+W+1)) (2*c*4^(2*d+1))) ≤ x:=(le_max_right ..).trans hx
  have bound:=(le_max_right _ _).trans mid
  have bc:0 < R.alloy.B.a.clock.hatBeta N:=by linarith only [hotN]
  have ceil:x ≤ 2*R.alloy.B.a.clock.hatBeta N:=by
    have hc:=Nat.ceil_lt_add_one bc.le
    change (Nat.ceil (R.alloy.B.a.clock.hatBeta N):ℝ) ≤ 2*R.alloy.B.a.clock.hatBeta N
    linarith only [hc,hotN]
  refine ⟨hotX,(le_max_left ..).trans mid,(le_max_left ..).trans bound,?_,?_⟩
  · intro l tl ln
    exact forced_budget b x _ _ (by linarith only [hotX]) bc ceil (forced t l N kl tl ln span).2
  · intro per p order g
    obtain ⟨gp,g1,band,fee⟩:=actual_band R N per (by linarith only [hotN])
    exact ⟨gp,g1,band,thermal_radius d p (by linarith only [hotX]) (zero_le_one.trans cp) gp.le g1 fee order ((le_max_right ..).trans bound)⟩

end YM.Integration.InletSusceptibility.Packet
