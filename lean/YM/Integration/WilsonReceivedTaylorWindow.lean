import YM.Integration.WilsonReceivedPhysicalFinite
import YM.Integration.WilsonFirstReceivedIssuedRoom

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedTaylorWindow
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor
open AllOrder AllOrder.Floe AllOrder.Transit PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open Further.PhysicalPeriodLimitF933 AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open Filter Pert.Asymptotics Comparison.RG02
open QuadraticLocal.Advent Org AllOrder.Floe.Step.PlanV
open scoped Classical BigOperators

/-- One later stage pays the actual returned row tariff at all periods and
ultraviolet cutoffs, throughout the physical axial window. -/
theorem funded {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (aperture : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
       Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (p shelf depth count : ℕ) (cap H : ℝ) (hc : 0 ≤ cap) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i+1 ≤ N → ∀ k : ℕ, k ≤ R.alloy.B.a.clock.J i →
      let X := R.family.path.levels.clock.hatBeta i
      let g := regulatorRun R.family N per (i+1)
      let B := R.family.path.levels.budget i
      let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)
      ∀ z : ℝ, |z| ≤ |H| *(Real.log X)^depth*((B.B:ℝ)^2*B.threshold)/g →
        WilsonReceivedSourceRoster.tariff G σ (cap*|z|) g p shelf * count ≤ ε*g^p := by
  let δ := ε/((count:ℝ)+1)
  have pos : (0:ℝ) < count+1 := by positivity
  have small : 0 < δ := div_pos ep pos
  let a := 2*(G.colorScale*cap)
  have a0 : 0 ≤ a := mul_nonneg (by norm_num) (mul_nonneg G.colorScale_pos.le hc)
  let d := p+shelf+2
  filter_upwards [WilsonFirstReceivedIssuedRoom.purchased R simple D φ aperture d depth a H a0 small,
    WilsonFirstReceivedIssuedRoom.purchased R simple D φ aperture 0 depth a H a0 small] with i budget unit
  intro N per hi k hk X g B σ z hz
  have h := budget N per hi k hk z hz
  have one := unit N per hi k hk z hz
  change (a*|z|/σ)^d * g ≤ δ at h
  change (a*|z|/σ)^0 * g ≤ δ at one
  have gain : (max 1 (a*|z|/σ))^d*g ≤ δ := by
    rcases le_total (a*|z|/σ) 1 with down|up
    · simpa only [max_eq_left down,one_pow,one_mul,pow_zero] using one
    · simpa only [max_eq_right up] using h
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have countPay : δ*(count:ℝ) ≤ ε :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) small.le).trans_eq (div_mul_cancel₀ ε pos.ne')
  have geometry : 2*(G.colorScale*(cap*|z|))/σ=a*|z|/σ := by dsimp [a]; ring
  rw [WilsonReceivedSourceRoster.tariff,geometry]
  calc
    _ = ((max 1 (a*|z|/σ))^d*g * count)*g^p := by dsimp [d]; rw [pow_succ]; ring
    _ ≤ (δ*(count:ℝ))*g^p := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right gain (Nat.cast_nonneg _)) (pow_nonneg gp _)
    _ ≤ ε*g^p := mul_le_mul_of_nonneg_right countPay (pow_nonneg gp _)

theorem potential {G : Gauge} (R : Run G) (simple : G.Simple) (depth : ℕ) (H : ℝ) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i+1 ≤ N →
      let X := R.family.path.levels.clock.hatBeta i
      let g := regulatorRun R.family N per (i+1)
      let B := R.family.path.levels.budget i
      ∀ z : ℝ, |z| ≤ |H| * (Real.log X)^depth*((B.B:ℝ)^2*B.threshold)/g →
        g ≤ 1 ∧ |z| ≤ 2*R.alloy.B.a.clock.hatBeta (i+1) := by
  let price := WilsonFirstReceivedRadialStencil.budget 1
  have lower : 1 ≤ price := by
    simpa only [Polynomial.eval_one, norm_one, abs_zero, add_zero, one_pow, one_mul, mul_one] using
      (WilsonFirstReceivedRadialStencil.priced (1 : Polynomial ℂ) (d:=1) (by simp) (A:=1) (fun _ _ => by simp) 0)
  have pp : 0 < price := zero_lt_one.trans_le lower
  filter_upwards [WilsonFirstReceivedRadialRoom.original R simple 1 depth H pp] with i issued
  intro N per live X g B z hz
  have cost := issued N per live z hz
  change price*(1+|z|)^1*g ≤ price at cost
  have inner : (1+|z|)*g ≤ 1 := by
    apply (mul_le_mul_iff_right₀ pp).mp
    simpa only [pow_one,mul_assoc,mul_one] using cost
  let β := (R.family.path.rep N per (i+1)).beta
  let upper := R.alloy.B.a.clock.hatBeta (i+1)
  have band := (R.makes.wilson.represents N per (i+1) live).band
  have b₀ : 0 < β := Overlay.beta_positive R.makes.wilson (show i < N by omega)
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr b₀)
  have one : 1 ≤ upper := (R.alloy.B.a.fits.delayed _).le
  have up : β ≤ 2*upper := band.2
  have rt : Real.sqrt β ≤ 2*upper := (Real.sqrt_le_iff).2 ⟨by positivity,by nlinarith [sq_nonneg (upper-1)]⟩
  have spl : g+|z| * g ≤ 1 := by simpa only [add_mul,one_mul] using inner
  refine ⟨by linarith only [spl,mul_nonneg (abs_nonneg z) gp.le],?_⟩
  calc
    |z| ≤ 1/g := (le_div_iff₀ gp).2 (by linarith only [spl,gp])
    _ = Real.sqrt β := by change 1/(Real.sqrt β)⁻¹=Real.sqrt β; simp
    _ ≤ _ := rt

end YM.Integration.WilsonReceivedTaylorWindow
