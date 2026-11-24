import YM.Integration.WilsonThermometerCompulsoryToll
import YM.Integration.WilsonOriginalThermometerTollBudget
import YM.Integration.WilsonReceivedFirstQEconomy

/-! The genuine first enrolled three-field posterior, with its physical test
radii removed at a cutoff-uniform perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryPower
open Filter MeasureTheory Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise AllOrder AllOrder.Floe.Step
open Pressure Push.PriceCompiler PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRent WilsonOriginalThermometerPalette
open WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTollBudget
open ConnectedActivityE6 QuadraticLocal.Rebirth Stationary Comparison.RG02 Push
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "A₀" => R.alloy.B.a
local notation "Y" j:max => R.alloy.B.a.clock.hatBeta j
local notation "J" => Stock.census (Fin 3)

def price := (2*rate R)^3*2*4^57

private theorem extend {i N per : ℕ} {f : Config G (R.family.side i per) → ℂ} {c d : ℝ}
    (pay : WilsonThermometerCompulsoryReturn.Heard R (top:=N) f c) (more : c ≤ d) :
    WilsonThermometerCompulsoryReturn.Heard R (top:=N) f d := by
  intro u hu
  have due := pay u hu
  refine ⟨fun U => (due.1 U).trans more,fun Z hz => ?_⟩
  have claim := due.2 Z hz
  exact ⟨claim.1,claim.2.trans (mul_le_mul_of_nonneg_left more (integral_nonneg fun U => norm_nonneg (Z U)))⟩

private theorem power {E Ω h y g C θ : ℝ} (n p : ℕ) (load : n ≤ 3)
    (E₀ : 0 ≤ E) (Ω₀ : 0 ≤ Ω) (h₀ : 0 ≤ h) (g₀ : 0 ≤ g) (θ₀ : 0 ≤ θ)
    (start : 1 ≤ y) (C₀ : 1 ≤ C) (paid : E*Ω ≤ C*y^11)
    (expense : Ω ≤ y) (radius : h ≤ 2*y^2) (coupling : y*g^2 ≤ 4) :
    (E*Ω^7*h)^n * (θ*(2*g^(p+114))) ≤ θ*((2*C)^3*2*4^57)*g^p := by
  have y₀ : 0 ≤ y := zero_le_one.trans start
  have Cpos : 0 ≤ C := zero_le_one.trans C₀
  have charge : E*Ω^7*h ≤ (2*C)*y^19 := by
    calc _ = (E*Ω)*Ω^6*h := by ring
         _ ≤ ((C*y^11)*y^6)*(2*y^2) := by
           exact mul_le_mul (mul_le_mul paid (pow_le_pow_left₀ Ω₀ expense 6) (pow_nonneg Ω₀ _) (by positivity))
             radius h₀ (by positivity)
         _ = _ := by ring
  have raised : (E*Ω^7*h)^n ≤ (2*C)^3*y^57 := by
    calc _ ≤ ((2*C)*y^19)^n := pow_le_pow_left₀ (by positivity) charge _
         _ ≤ ((2*C)*y^19)^3 := pow_le_pow_right₀
           (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ start)) load
         _ = _ := by ring
  have tail : y^57*g^(p+114) ≤ 4^57*g^p := by
    calc _ = (y*g^2)^57*g^p := by rw [pow_add]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) coupling 57) (pow_nonneg g₀ _)
  calc _ ≤ ((2*C)^3*y^57)*(θ*(2*g^(p+114))) :=
             mul_le_mul_of_nonneg_right raised (mul_nonneg θ₀ (mul_nonneg (by norm_num) (pow_nonneg g₀ _)))
       _ = (θ*((2*C)^3*2))*(y^57*g^(p+114)) := by ring
       _ ≤ (θ*((2*C)^3*2))*(4^57*g^p) := mul_le_mul_of_nonneg_left tail (by positivity)
       _ = _ := by ring

theorem original (simple : G.Simple)
    (D : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ : ℕ → ℕ) (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay) (p : ℕ) :
    ∀ᶠ j : ℕ in atTop, ∀ N per : ℕ, j+1<N → ∀ k : ℕ,
    k ≤ (A₀).clock.J ((j+1)+1) → reach R ≤ (A₀).clock.J ((j+1)+1)+1 →
    let g := Coat.gStep (R.family.path.rep N per (j+1)).beta
    let g' := Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
    let E := max 1 ((1+WilsonOriginalThermometerTopGrading.cap R (j+1) 1)*
      wallet R levels (Poetry.Agenda.seed D φ k ((A₀).clock.J ((j+1)+1))))
    ∀ s : (Stock.census (Fin 3)).Mode, ∀ first now : Fin 3 → ℝ, ∀ (Ω h rent ε θ : ℝ) (grade : ℕ),
      0<Ω → Ω ≤ Advent.budgetR R (j+1) → 0<h → rent≤1 → 0≤ε → ε≤1 → 0≤θ →
      h ≤ max 1 (max (Advent.budgetR R j*Advent.budgetR R (j+1)) (rent+ε*g'^grade)) →
      Poly.toll first s*(E*Ω)^s.val.card=1 → (∀ a, now a=first a/(Ω^6*h)) →
      ∀ f : Config G (R.family.side j per) → ℂ,
      WilsonThermometerCompulsoryReturn.Heard R (top:=N) (fun U => Poly.toll now s • f U) (θ*(2*g^(p+114))) →
      WilsonThermometerCompulsoryReturn.Heard R (top:=N) f (θ*price R*g^p) := by
  filter_upwards [WilsonReceivedFirstQEconomy.physical R simple] with j good N per cut k caught extent
  let y := Y ((j+1)+1)
  let g := Coat.gStep (R.family.path.rep N per (j+1)).beta
  let g' := Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
  let E := max 1 ((1+WilsonOriginalThermometerTopGrading.cap R (j+1) 1)*
    wallet R levels (Poetry.Agenda.seed D φ k ((A₀).clock.J ((j+1)+1))))
  dsimp only
  intro s first now Ω h rent ε θ grade sale cap cash old ε₀ ε₁ signed radius top next f pay
  have cool := good N per cut
  have y₁ : 1 ≤ y := ((A₀).fits.delayed ((j+1)+1)).le
  have y₀ : 0 ≤ y := zero_le_one.trans y₁
  have g₀ : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have g'₀ : 0 ≤ g' := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have up : Y (j+1) ≤ y := by
    dsimp only [y]
    rw [beta_eq R.alloy.B.valid (j+1)]
    exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le
      (Real.log_nonneg (Nat.one_le_cast.mpr (R.rolls.L _).property)))
  have upper := WilsonOriginalThermometerTollBudget.parameter R (j+1)
  have lower := (WilsonOriginalThermometerTollBudget.parameter R j).trans up
  have y₂ : 1 ≤ y^2 := one_le_pow₀ y₁
  have both : Advent.budgetR R j*Advent.budgetR R (j+1) ≤ y^2 := by
    rw [pow_two]
    exact mul_le_mul lower upper (sale.le.trans cap) y₀
  have ordinary : g'^grade ≤ 1 := pow_le_one₀ g'₀ cool.2.1
  have small : ε*g'^grade ≤ 1 := ((mul_le_mul_of_nonneg_left ordinary ε₀).trans_eq (mul_one ε)).trans ε₁
  have bound : h ≤ 2*y^2 := radius.trans (max_le (by linarith) (max_le (by linarith only [both,y₂])
    (by linarith only [old,small,y₂])))
  have paid : E*Ω ≤ rate R*y^11 :=
    WilsonOriginalThermometerTollBudget.original R simple D φ income (j+1) k caught extent sale.le cap
  have receipt := WilsonThermometerCompulsoryToll.original R (by omega : j ≤ N) s
    (zero_le_one.trans (le_max_left _ _)) sale cash top next pay
  apply extend R receipt
  have load : s.val.card ≤ 3 := s.val.card_le_univ.trans_eq (by decide)
  exact power s.val.card p load (zero_le_one.trans (le_max_left _ _)) sale.le cash.le g₀ signed y₁
    (le_max_left _ _) paid (cap.trans upper) bound cool.2.2

end YM.Integration.WilsonThermometerCompulsoryPower
end
