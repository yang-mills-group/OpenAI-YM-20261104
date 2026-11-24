import YM.Integration.WilsonReflectedAffordableArm
/-! Relative-scale version of the fixed-date purchase. The true native
one-step stock at K uses one of the paid exponents of the *relative*
interval, including when the original reporting mesh tends to zero. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedRelativeDate
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "c" j:max => (C₀).S.scale j

theorem monotone : Monotone (C₀).S.scale:=by
  intro m n h
  simp only [Schedule.scale,Real.log_inv]
  exact neg_le_neg (Real.log_le_log ((C₀).S.a_pos n) ((C₀).S.strictAnti.antitone h))

theorem ratio (f K:ℕ):Real.log ((C₀).S.a f/(C₀).S.a K)=c K-c f:=by
  rw [Real.log_div ((C₀).S.a_pos f).ne' ((C₀).S.a_pos K).ne']
  simp only [Schedule.scale,Real.log_inv];ring

theorem source : ∀ᶠ K:ℕ in atTop,∀f,f<K→1+4*stock (C₀) K≤2*Real.exp ((c K-c f)/32):=by
  obtain ⟨i,bank⟩:=eventually_atTop.mp (factor_large (C₀) (1/32) (by norm_num))
  filter_upwards [eventually_ge_atTop (i+1)] with K late
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show K≠0 by omega)
  intro f fk
  have h:4*stock (C₀) (k+1)≤(factor (C₀) k)^(1/32:ℝ):=(bank k (by omega)).2
  have m:=monotone R (show f≤k by omega)
  have mn:=monotone R fk.le
  have one:1≤Real.exp ((c (k+1)-c f)/32):=Real.one_le_exp (by linarith only [mn])
  have l:Real.log (factor (C₀) k)≤c (k+1)-c f:=by
    rw [(C₀).S.scale_succ];dsimp only [factor];linarith only [m]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans (factor_positive (C₀) k))] at h
  have t:=h.trans (Real.exp_le_exp.mpr (show Real.log (factor (C₀) k)*(1/32)≤(c (k+1)-c f)/32 by linarith only [l]))
  linarith only [one,t]

theorem account : ∀ᶠ K:ℕ in atTop,∀(d j f:ℕ),f<K→
    (((C₀).S.a j)/((C₀).S.a f))^d*hike (C₀) K f rate*(1+4*stock (C₀) K)*stretch R (1/32) j K≤
      4*Real.exp (((d:ℝ)+1/32)*(c f-c j)-(c K-c f)/16):=by
  filter_upwards [source R] with K wallet
  intro d j f fk
  have hstep:=wallet f fk
  have hk:0≤hike (C₀) K f rate:=Real.rpow_nonneg (div_nonneg ((C₀).S.a_pos K).le ((C₀).S.a_pos f).le) _
  have hs:0≤WilsonOriginalMicroscopicGuardedReporters.stretch R (1/32) j K:=by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity
  have hd:0≤(((C₀).S.a j)/((C₀).S.a f))^d:=pow_nonneg (div_nonneg ((C₀).S.a_pos j).le ((C₀).S.a_pos f).le) d
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep (mul_nonneg hd hk)) hs).trans_eq
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (div_pos ((C₀).S.a_pos j) ((C₀).S.a_pos f)),ratio R j f,
    hike,Real.rpow_def_of_pos (div_pos ((C₀).S.a_pos K) ((C₀).S.a_pos f)),ratio R K f]
  unfold WilsonOriginalMicroscopicGuardedReporters.stretch
  rw [show ∀x y z w:ℝ,x*y*(2*z)*(2*w)=4*(x*y*z*w) by intros;ring]
  simp only [←Real.exp_add];congr 2;unfold rate;ring

end YM.Integration.WilsonReflectedRelativeDate
end
