import YM.Integration.WilsonOriginalClockFacePosterior
import YM.Integration.WilsonOriginalSeparatedMask

/-! The native marked crop occupies a polylogarithmic number of lower sites.
This estimate is uniform on the true Wilson clocks at both ends of the collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFailedFaceCalendar
open Filter Finset Lattice Wilson RG Marker QuadraticLocal PhysicalNext PhysicalNext.Repeat.Legato
open Pert.Asymptotics WilsonOriginalSeparatedMask
open scoped Classical BigOperators

private def radius (A:ℝ):ℝ:=10*(2*A+1)+4

private theorem crop {B h:ℕ}{x A:ℝ}(large:1 ≤ x)(pos:0 ≤ A)
    (bank:(B:ℝ) ≤ 2*x^2)(cut:(h:ℝ) ≤ (2*A+1)*x):
    ((max B (reach B h)+max B (reach B h)+1:ℕ):ℝ)^4 ≤ (2*radius A+1)^4*x^12:=by
  have xp:0 ≤ x:=zero_le_one.trans large
  have two:1 ≤ x^2:=one_le_pow₀ large
  have three:1 ≤ x^3:=one_le_pow₀ large
  have inc:x^2 ≤ x^3:=pow_le_pow_right₀ large (by decide)
  have brim:4*(B:ℝ)+2 ≤ 10*x^2:=by linarith only [bank,two]
  have hh:0 ≤ 2*A+1:=by linarith
  have stems:((h*(4*B+2):ℕ):ℝ) ≤ 10*(2*A+1)*x^3:=by
    push_cast
    calc _ ≤ ((2*A+1)*x)*(10*x^2):=mul_le_mul cut brim (by positivity) (mul_nonneg hh xp)
         _ = _:=by ring
  have paid:((max B (reach B h):ℕ):ℝ) ≤ radius A*x^3:=by
    rw [Nat.cast_max]
    apply max_le
    · unfold radius
      nlinarith only [bank,inc,mul_nonneg hh (pow_nonneg xp 3)]
    · change ((h*(4*B+2)+2*B:ℕ):ℝ) ≤ _
      push_cast at stems ⊢
      unfold radius
      linarith only [stems,inc,bank]
  have diameter:((max B (reach B h)+max B (reach B h)+1:ℕ):ℝ) ≤ (2*radius A+1)*x^3:=by
    push_cast at paid ⊢
    linarith only [paid,three]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) diameter 4).trans_eq (by ring)

private def invoice (n:ℕ)(A tol:ℝ):ℝ:=
  n*(2*radius A+1)^4*(4*Real.exp 102)*tol*2

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j

include simple in
theorem original (n:ℕ){A tol:ℝ}(ap:0 ≤ A)(tp:0 ≤ tol):
    ∀ᶠ b:ℕ in atTop,∀{i N per:ℕ}(_bi:b ≤ i)(_live:i ≤ N){B h seats q p:ℕ}{α tilt:ℝ},
    B=Nat.ceil ((Real.log (H i))^2) → α ≤ 100 → seats ≤ n →
    h ≤ Nat.ceil (A*(1+Real.log (regulatorRun R.family N per b)⁻¹)) →
    0 ≤ tilt → tilt ≤ 2 → q+2 ≤ p →
    ((seats*(max B (reach B h)+max B (reach B h)+1)^4:ℕ):ℝ)*
      (4*Real.exp (α+2))*tol/(H i)^p*tilt ≤ (regulatorRun R.family N per b)^q:=by
  have grow:=Next.Rank.Station.hat_rate R.family.path.levels simple
  have logs:=grow.eventually ((Real.isLittleO_pow_log_id_atTop (n:=12)).bound (by norm_num:0<(1:ℝ)))
  have stage:∀ᶠ i:ℕ in atTop,Real.exp 1 ≤ H i ∧ 2 ≤ H i ∧
      invoice n A tol ≤ H i ∧ (Real.log (H i))^12 ≤ H i:=by
    filter_upwards [grow.eventually_ge_atTop (Real.exp 1),grow.eventually_ge_atTop 2,
      grow.eventually_ge_atTop (invoice n A tol),logs] with i one two wage logFee
    have pos:0<H i:=by linarith only [two]
    have gate:0 ≤ Real.log (H i):=Real.log_nonneg (by linarith)
    exact ⟨one,two,wage,by simpa [Real.norm_eq_abs,abs_of_pos pos,abs_of_nonneg gate] using logFee⟩
  obtain ⟨start,after⟩:=eventually_atTop.mp stage
  filter_upwards [eventually_ge_atTop start] with b late
  intro i N per bi live B h seats q p α tilt size fixed count cut sign spring order
  let χ:=H i
  let x:=Real.log χ
  let g:=regulatorRun R.family N per b
  have pack:=after i (late.trans bi)
  have two:2 ≤ χ:=pack.2.1
  have cp:0<χ:=by linarith only [two]
  have large:1 ≤ x:=(Real.le_log_iff_exp_le cp).mpr pack.1
  have xp:0 ≤ x:=zero_le_one.trans large
  have pow12:0 ≤ x^12:=pow_nonneg xp _
  have temp:(R.family.path.β N per b) ≤ 2*χ:=
    (R.makes.wilson.represents N per b (bi.trans live)).band.2.trans
      (mul_le_mul_of_nonneg_left (WilsonStartup.Timing.hat_mono R.family.path.levels
        (Gauge.slopeConstant_pos simple).le bi) (by norm_num))
  have root:(g)⁻¹ ≤ χ:=by
    change ((Real.sqrt (R.family.path.β N per b))⁻¹)⁻¹ ≤ χ
    rw [inv_inv,Real.sqrt_le_iff]
    exact ⟨cp.le,temp.trans (by nlinarith only [mul_nonneg cp.le (sub_nonneg.mpr two)])⟩
  have gp:0<g:=IterationFour.Currency.g_pos R.makes N per b (bi.trans live)
  have logs':Real.log g⁻¹ ≤ x:=Real.log_le_log (inv_pos.mpr gp) root
  have size':(B:ℝ) ≤ 2*x^2:=by
    rw [size]
    exact (Nat.ceil_lt_add_one (sq_nonneg x)).le.trans (by linarith only [one_le_pow₀ large (n:=2)])
  have hh:(h:ℝ) ≤ (2*A+1)*x:=by
    have cap:h ≤ Nat.ceil (A*(1+x)):=cut.trans (Nat.ceil_mono (mul_le_mul_of_nonneg_left (by linarith only [logs']) ap))
    calc _ ≤ (Nat.ceil (A*(1+x)):ℝ):=by exact_mod_cast cap
         _ ≤ A*(1+x)+1:=(Nat.ceil_lt_add_one (mul_nonneg ap (by linarith only [large]))).le
         _ ≤ _:=by nlinarith only [large,mul_nonneg ap (sub_nonneg.mpr large)]
  have width:=crop large ap size' hh
  have expense:((seats*(max B (reach B h)+max B (reach B h)+1)^4:ℕ):ℝ)*(4*Real.exp (α+2))*tol*tilt
      ≤ χ^2:=by
    have ann:Real.exp (α+2) ≤ Real.exp 102:=Real.exp_le_exp.mpr (by linarith only [fixed])
    have full:((seats*(max B (reach B h)+max B (reach B h)+1)^4:ℕ):ℝ)*(4*Real.exp (α+2))*tol*tilt
        ≤ ((n:ℝ)*((2*radius A+1)^4*x^12))*(4*Real.exp 102)*tol*2:=by
      push_cast at width ⊢
      gcongr
    calc _ ≤ _:=full
         _ = invoice n A tol*x^12:=by unfold invoice;ring
         _ ≤ χ*χ:=mul_le_mul pack.2.2.1 pack.2.2.2 pow12 cp.le
         _ = _:=by ring
  have inv:χ⁻¹ ≤ g:=by simpa using inv_anti₀ (inv_pos.mpr gp) root
  calc _ = (((seats*(max B (reach B h)+max B (reach B h)+1)^4:ℕ):ℝ)*(4*Real.exp (α+2))*tol*tilt)/χ^p:=by ring
       _ ≤ χ^2/χ^p:=div_le_div_of_nonneg_right expense (pow_nonneg cp.le _)
       _ ≤ χ^2/χ^(q+2):=div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos cp _) (pow_le_pow_right₀ (by linarith only [two]) order)
       _ = (χ⁻¹)^q:=by rw [pow_add,inv_pow]; field_simp
       _ ≤ _:=pow_le_pow_left₀ (inv_nonneg.mpr cp.le) inv q

end YM.Integration.WilsonOriginalFailedFaceCalendar
end
