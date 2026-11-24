import YM.Integration.WilsonPositiveFourHardReserve
import YM.Integration.WilsonOriginalOccupiedSource

/-! A single legal amplitude for all genuine mixed and hard rows at a
separated physical date. Its inverse leaves a quadratic logarithmic reserve. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalTapRate
open Function Finset Filter Lattice Wilson RG Source Pressure
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato ActualRunKernelPackets Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open WilsonOriginalOccupiedSource WilsonOriginalOccupiedStencil
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

def value(f:ℕ):ℝ:=Real.exp ((Real.log (H f))^2/32)

theorem original (simple:G.Simple)(n:ℕ):
    ∀ᶠ f:ℕ in atTop,∀z∈nodes n (value R f:ℂ),
      4*‖z‖≤Real.exp ((((A).budget f).B/8:ℕ):ℝ) ∧
      ‖z‖*LocalComparison.forcedDivisor R.family f≤1:=by
  have grows:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)
  filter_upwards [grows.eventually_ge_atTop (128*((n:ℝ)+1)),WilsonPositiveFourHardReserve.cube R simple] with f hot hard z hz
  let y:=Real.log (H f)
  let E:=value R f
  have now:128*((n:ℝ)+1)≤y:=hot
  have ybig:128≤y:=by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have amount:1≤E:=by exact Real.one_le_exp (div_nonneg (sq_nonneg y) (by norm_num))
  have ep:0<E:=by linarith only [amount]
  have gross:4*((n:ℝ)+1)≤E:=by
    change 4*((n:ℝ)+1)≤Real.exp (y^2/32)
    refine le_trans ?_ (Real.add_one_le_exp _)
    nlinarith only [now,ybig,mul_nonneg (by linarith only [ybig]:0≤y) (by linarith only [ybig]:0≤y-1)]
  have reachable:‖z‖≤((n:ℝ)+1)*E:=by
    simp only [nodes,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hz
    rcases hz with rfl|rfl|⟨i,rfl⟩
    · rw [norm_one];nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    · rw [norm_zero];positivity
    · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ep.le]
      have ij:(i.val:ℝ)≤(n:ℝ)+1:=by exact_mod_cast i.isLt.le
      change E*‖(i.val:ℂ)‖≤((n:ℝ)+1)*E
      rw [Complex.norm_natCast,mul_comm]
      exact mul_le_mul_of_nonneg_right ij ep.le
  have squared:4*‖z‖≤Real.exp (y^2/16):=by
    calc
      _ ≤ 4*(((n:ℝ)+1)*E):=mul_le_mul_of_nonneg_left reachable (by norm_num)
      _ ≤ E*E:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right gross ep.le
      _ = Real.exp (y^2/16):=by change Real.exp _*Real.exp _=_;rw [←Real.exp_add];congr 1;ring
  have geom:((A).budget f).B≤8*(((A).budget f).B/8)+7:=by omega
  have extent:y^2≤(((A).budget f).B:ℝ):=Nat.le_ceil _
  have slots:(((A).budget f).B:ℝ)≤8*((((A).budget f).B/8:ℕ):ℝ)+7:=by exact_mod_cast geom
  refine ⟨squared.trans (Real.exp_le_exp.mpr (by nlinarith only [extent,slots,ybig,sq_nonneg (y-64)])),?_⟩
  have one:‖z‖≤Real.exp (y^2/16):=by linarith [norm_nonneg z]
  have both:‖z‖*LocalComparison.forcedDivisor R.family f≤Real.exp (y^2/16)*Real.exp (-y^3):=
    mul_le_mul one hard (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  refine both.trans ?_
  rw [←Real.exp_add,Real.exp_le_one_iff]
  nlinarith only [mul_nonneg (sq_nonneg y) (by linarith only [ybig]:0≤y-1)]

end YM.Integration.WilsonSeparatedPrefixCanonicalTapRate
