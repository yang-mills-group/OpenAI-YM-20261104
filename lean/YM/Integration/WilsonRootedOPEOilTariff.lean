import YM.Integration.WilsonRootedOPEPointFloor

/-! The actual ultraviolet calendar and the finite MS oil polynomial give an
absolute price before every period or point is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEOilTariff
open Finset Lattice Wilson RG PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "β" => R.family.path.levels.clock.hatBeta

include simple in
theorem argument (μ:ℝ) : ∃C:ℝ,0<C ∧ ∀N,|μ-R.family.S.scale N| ≤ C*β N := by
  have sp:=Gauge.slopeConstant_pos simple
  refine ⟨|μ|+G.slopeConstant⁻¹,add_pos_of_nonneg_of_pos (abs_nonneg _) (inv_pos.mpr sp),?_⟩
  intro N
  have leOne:R.family.S.a N ≤ 1 := (R.family.S.strictAnti.antitone (Nat.zero_le N)).trans_eq (R.family.S.a_zero)
  have s:0 ≤ R.family.S.scale N := Real.log_nonneg ((one_le_inv₀ (R.family.S.a_pos N)).mpr leOne)
  have origin := R.family.path.levels.clock.bar_pos
  have mesh: G.slopeConstant * R.family.S.scale N ≤ β N := by
    change G.slopeConstant * R.family.S.scale N ≤ R.family.path.levels.clock.bar + G.slopeConstant * R.family.S.scale N
    linarith only [origin]
  have cap : R.family.S.scale N ≤ G.slopeConstant⁻¹*β N := by
    rw [←div_eq_inv_mul];apply (le_div_iff₀ sp).mpr
    simpa only [mul_comm] using mesh
  calc
    |μ-R.family.S.scale N| ≤ |μ|+R.family.S.scale N := (abs_sub _ _).trans_eq (by rw [abs_of_nonneg s])
    _ ≤ |μ| * β N + G.slopeConstant⁻¹*β N := add_le_add (le_mul_of_one_le_right (abs_nonneg _) (R.family.path.levels.fits.delayed N).le) cap
    _ = _ := (add_mul ..).symm

include simple in
theorem polynomial (μ:ℝ) (P:Polynomial ℝ) : ∃C:ℝ,0≤C ∧ ∀N,|P.eval (μ-R.family.S.scale N)| ≤ C*β N^P.natDegree := by
  obtain ⟨c,cp,all⟩ := argument R simple μ
  let t:=P.natDegree
  let M:=∑i∈range (t+1),|P.coeff i| * c^i
  refine ⟨M,sum_nonneg fun i _=>mul_nonneg (abs_nonneg _) (pow_nonneg cp.le _),?_⟩
  intro N
  let z:=μ-R.family.S.scale N
  have one := (R.family.path.levels.fits.delayed N).le
  have terms (i:ℕ) (mem:i∈range (t+1)) : |P.coeff i*z^i| ≤ (|P.coeff i| * c^i)*β N^t := by
    rw [abs_mul,abs_pow]
    have b:=pow_le_pow_left₀ (abs_nonneg z) (all N) i
    rw [mul_pow] at b
    have degree: i≤t := by have h:=mem_range.mp mem;omega
    calc
      _ ≤ |P.coeff i| * (c^i*β N^i) := mul_le_mul_of_nonneg_left b (abs_nonneg _)
      _ = (|P.coeff i| * c^i)*β N^i := (mul_assoc ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one degree) (mul_nonneg (abs_nonneg _) (pow_nonneg cp.le _))
  change |P.eval z| ≤ M*β N^t
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self P.natDegree)]
  calc
    _ ≤ _ := abs_sum_le_sum_abs ..
    _ ≤ ∑i∈range (t+1),(|P.coeff i| * c^i)*β N^t := sum_le_sum terms
    _ = _ := (sum_mul ..).symm

end YM.Integration.WilsonRootedOPEOilTariff
