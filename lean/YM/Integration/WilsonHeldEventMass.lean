import YM.Integration.ActualScalarTransport
import YM.Integration.WilsonRegisteredRegularQuota

/-! A moving signed tester on two consecutive genuine Wilson fields. Its
bound on the inspected event is returned against the upper physical mass
after integrating the unchanged lower conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldEventMass
open Function Set MeasureTheory Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge} (R : Run G) {N per m : ℕ}

theorem original (live : m<N) {D:Set (Config G (R.family.side (m+1) per))} (md:MeasurableSet D)
    (H:Config G (R.family.side m per) → Config G (R.family.side (m+1) per)→ℝ)
    (M:ℝ) (hp:0≤M) (bound:∀ V U,U∈D→|H V U|≤M) :
    (∫V,‖actualAverage R.family (N:=N) (D.indicator (H V)) V‖
      ∂scene R.family.path N per m) ≤ M*(scene R.family.path N per (m+1)).real D := by
  let e:=D.indicator (fun _=>M)
  have me:Measurable e:=measurable_const.indicator md
  have en U:0≤e U:=Set.indicator_nonneg (fun _ _=>hp) U
  have eb U:‖e U‖≤M:=by
    rw [Real.norm_of_nonneg (en U)]
    by_cases u:U∈D <;> simp [e,u,hp]
  have compare (V:Config G (R.family.side m per)) :
      ‖actualAverage R.family (N:=N) (D.indicator (H V)) V‖≤actualAverage R.family (N:=N) e V := by
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _)
      (actualAverage_integrable R.family R.makes live me.aestronglyMeasurable eb V)
    apply ae_of_all
    intro U
    change ‖actualConditionalDensity R.family N per m V U • D.indicator (H V) U‖≤
      actualConditionalDensity R.family N per m V U • e U
    rw [norm_smul,Real.norm_of_nonneg (actualConditionalDensity_nonneg R.family R.makes live V U)]
    apply mul_le_mul_of_nonneg_left _ (actualConditionalDensity_nonneg R.family R.makes live V U)
    by_cases u:U∈D
    · simpa only [e,Set.indicator_of_mem u,Real.norm_eq_abs] using bound V U u
    · simp [e,u]
  have one:actualTransport R.family (N:=N) e (Nat.le_succ m)=actualAverage R.family (N:=N) e:=by
    rw [actualTransport_step R.family R.makes live e (Nat.lt_succ_self m),actualTransport_base R.family R.makes live]
  have weighted:=actualTransport_weighted_integrable R.family R.makes live
    (me.aestronglyMeasurable (μ:=prior G _)) eb le_rfl
  rw [actualTransport_base R.family R.makes live] at weighted
  have old:=actualTransport_weighted_integrable R.family R.makes live
    (me.aestronglyMeasurable (μ:=prior G _)) eb (Nat.le_succ m)
  have use:=actualScene_integrable_of_weighted R.family R.makes (Nat.le_of_lt live) old
  rw [one] at use
  have mean:=actualScene_transport R.family R.makes live weighted (Nat.le_succ m)
  rw [one] at mean
  calc
    _ ≤ ∫V,actualAverage R.family (N:=N) e V ∂scene R.family.path N per m :=
      integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) use (ae_of_all _ compare)
    _ = ∫U,e U ∂scene R.family.path N per (m+1) := mean
    _ = _ := by rw [integral_indicator_const _ md];simp [smul_eq_mul,mul_comm]

end YM.Integration.WilsonHeldEventMass
end
