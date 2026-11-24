import YM.Integration.WilsonReflectedFundedHearing
/-! The fixed-date inverse and its genuine original hard tariff are
absorbed by the null decay on the same original history, before both
regulators. All participating finite source norms can be paid at once. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedRestartDate
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonReflectedFullPanel WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonReflectedFundedHearing
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "c" j:max => (C₀).S.scale j

private theorem since (j:ℕ):0≤c j:=by
  apply Real.log_nonneg
  apply (one_le_inv₀ ((C₀).S.a_pos j)).2
  simpa using (C₀).S.strictAnti.antitone (Nat.zero_le j)

private theorem stable (K f:ℕ):hike (C₀) K f rate=Real.exp (rate*(c f-c K)):=by
  rw [hike,Real.rpow_def_of_pos (div_pos ((C₀).S.a_pos K) ((C₀).S.a_pos f)),
    Real.log_div ((C₀).S.a_pos K).ne' ((C₀).S.a_pos f).ne']
  simp only [Schedule.scale,Real.log_inv]
  congr 1;ring

theorem source : ∀ᶠ K:ℕ in atTop,1+4*stock (C₀) K≤2*Real.exp ((c K)/32):=by
  obtain ⟨i,bank⟩:=eventually_atTop.mp (factor_large (C₀) (1/32) (by norm_num))
  filter_upwards [eventually_ge_atTop (i+1)] with K late
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show K≠0 by omega)
  have h:4*stock (C₀) (k+1)≤(factor (C₀) k)^(1/32:ℝ):=(bank k (by omega)).2
  have one: 1≤Real.exp (c (k+1)/32):=Real.one_le_exp (div_nonneg (since R (k+1)) (by norm_num))
  have step:Real.log (factor (C₀) k)≤c (k+1):=by
    rw [(C₀).S.scale_succ];linarith only [since R k]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans (factor_positive (C₀) k))] at h
  have next:=h.trans (Real.exp_le_exp.mpr (show Real.log (factor (C₀) k)*(1/32)≤c (k+1)/32 by linarith only [step]))
  linarith only [one,next]

theorem decay (f:ℕ): ∀ᶠ K:ℕ in atTop,∀j,
    hike (C₀) K f rate*(1+4*stock (C₀) K)*stretch R (1/32) j K≤
    4*Real.exp (rate*c f)*Real.exp (-(c K)/16):=by
  filter_upwards [source R] with K cut
  intro j
  have inc:stretch R (1/32) j K≤2*Real.exp (c K/32):=by
    apply mul_le_mul_of_nonneg_left _ (by norm_num:0≤(2:ℝ))
    apply Real.exp_le_exp.mpr;linarith only [since R j]
  have sp:0 ≤ stretch R (1/32) j K:=by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity
  rw [stable]
  calc
    _ ≤ (Real.exp (rate*(c f-c K))*(2*Real.exp (c K/32)))*(2*Real.exp (c K/32)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left cut (Real.exp_pos _).le) inc sp (by positivity)
    _ = _ :=by
      rw [show Real.exp (rate*(c f-c K))*(2*Real.exp (c K/32))*(2*Real.exp (c K/32))=
        4*(Real.exp (rate*(c f-c K))*Real.exp (c K/32)*Real.exp (c K/32)) by ring,
        ←Real.exp_add,←Real.exp_add,mul_assoc,←Real.exp_add]
      congr 2;unfold rate;ring

theorem before_cutoffs (f:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠ K:ℕ in atTop,∀j,hike (C₀) K f rate*(1+4*stock (C₀) K)*stretch R (1/32) j K≤ε:=by
  let T:=4*Real.exp (rate*c f)
  have pos:0<T:=by unfold T;positivity
  filter_upwards [decay R f,(C₀).S.divergent.eventually_ge_atTop (-16*Real.log (ε/T))] with K paid late
  intro j
  apply (paid j).trans
  have h:Real.exp (-(c K)/16)≤ε/T:=by
    rw [←Real.exp_log (div_pos ep pos)]
    apply Real.exp_le_exp.mpr
    linarith only [late]
  exact (mul_le_mul_of_nonneg_left h pos.le).trans_eq (by field_simp)

end YM.Integration.WilsonReflectedRestartDate
end
