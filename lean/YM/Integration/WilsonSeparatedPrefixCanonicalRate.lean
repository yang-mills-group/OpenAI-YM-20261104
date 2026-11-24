import YM.Integration.WilsonSeparatedPrefixCanonicalTapRate
import YM.Integration.WilsonReflectedPublicOpticalDuration

/-! The native separated support pays the complete repeated flat return on
the actual optical interval. The onset precedes the cutoff and period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalRate
open Function Filter Finset Real Lattice Wilson RG Source Precision RG16 PhysicalNext.Repeat.Legato Marker
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

theorem original (simple:G.Simple)(run:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (A₀ D m P:ℕ)(C:ℝ)(cp:0≤C):
    ∀ᶠ j:ℕ in atTop,∀f:ℕ,j≤f → R.family.S.a j/R.family.S.a f≤(H f)^A₀ →
    C*((H f)^(D+6*(f-j)*m))*(WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹≤((H f)^P)⁻¹:=by
  let ε:ℝ:=(1024*((m:ℝ)+1))⁻¹
  have ep:0<ε:=by dsimp [ε];positivity
  have grows:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)
  obtain ⟨j₀,late⟩:=eventually_atTop.mp (grows.eventually_ge_atTop (128*(C+(D:ℝ)+(P:ℝ)+1)))
  obtain ⟨j₁,heat⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate (A) simple).eventually_ge_atTop 1)
  filter_upwards [WilsonReflectedPublicOpticalDuration.original R simple run A₀ ep,
    eventually_ge_atTop (max j₀ j₁)] with j duration paid f jf span
  let y:=Real.log (H f)
  let hours:ℝ:=(f-j:ℕ)
  have warm:1≤H f:=heat f (by omega)
  have hp:0<H f:=by linarith
  have big:128*(C+(D:ℝ)+(P:ℝ)+1)≤y:=late f (by omega)
  have yp:1≤y:=by linarith [Nat.cast_nonneg (α:=ℝ) D,Nat.cast_nonneg (α:=ℝ) P]
  have hd:hours≤ε*y:=duration f jf span
  have mpos:0<(m:ℝ)+1:=by positivity
  have time:hours*((m:ℝ)+1)≤y/1024:=by
    calc
      _ ≤ ε*y*((m:ℝ)+1):=mul_le_mul_of_nonneg_right hd mpos.le
      _ = y/1024 :=by dsimp [ε];field_simp
  have tt:hours*(m:ℝ)*y≤y^2/1024:=by
    have hn:0≤hours:=Nat.cast_nonneg _
    have short:hours*(m:ℝ)≤y/1024:=by linarith
    nlinarith only [mul_le_mul_of_nonneg_right short (le_trans zero_le_one yp)]
  have ds: (C+(D:ℝ)+(P:ℝ)+1)*y≤y^2/128:=by
    nlinarith only [mul_le_mul_of_nonneg_right big (le_trans zero_le_one yp)]
  have fe:C≤Real.exp C:=by linarith [Real.add_one_le_exp C]
  have repr(n:ℕ):(H f)^n=Real.exp ((n:ℝ)*y):=by
    rw [←Real.log_pow,Real.exp_log (pow_pos hp _)]
  have debit:C+((D:ℝ)+6*hours*(m:ℝ))*y-y^2/32≤-(P:ℝ)*y:=by
    nlinarith only [tt,ds,mul_nonneg cp (sub_nonneg.mpr yp),yp]
  calc
    _ ≤ Real.exp C*(H f)^(D+6*(f-j)*m)*(WilsonSeparatedPrefixCanonicalTapRate.value R f)⁻¹:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right fe (pow_nonneg hp.le _)) (inv_nonneg.mpr (Real.exp_nonneg _))
    _ = Real.exp (C+((D:ℝ)+6*hours*(m:ℝ))*y-y^2/32):=by
      rw [repr]
      change Real.exp C*Real.exp _*(Real.exp (y^2/32))⁻¹=_
      rw [←Real.exp_neg,←Real.exp_add,←Real.exp_add]
      push_cast
      dsimp [hours]
      congr 1
    _ ≤ Real.exp (-(P:ℝ)*y):=Real.exp_le_exp.mpr debit
    _ = _:=by rw [repr,←Real.exp_neg,neg_mul]

end YM.Integration.WilsonSeparatedPrefixCanonicalRate
