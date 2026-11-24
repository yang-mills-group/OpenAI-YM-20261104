import YM.Integration.WilsonOriginalTwoDateQHistory
import YM.Integration.WilsonReceivedCloseChainFunding

/-! The two genuine radius bills at a new physical source, fixed before the signed comparison order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseBirthPrice
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open Pert.Asymptotics
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (request : Request V) (freshQ : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ) (free : V → ℝ)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (K : ℕ) (freePos : ∀v,0<free v)
  (warm : QuadraticLocal.Spill.Raffle.Warm G D R.alloy.delay φ)

local notation "primary" => WilsonOriginalMixedFiniteVoter.original R request freshQ u μ extra free D income simple K 0 freePos (ε:=1) zero_lt_one
local notation "second" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos
local notation "C₁" => Classical.choose primary
local notation "C₂" => Classical.choose second
local notation "d₁" => (Classical.choose_spec primary).2.choose
local notation "d₂" => (Classical.choose_spec second).2.choose
local notation "tollQ" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "padQ" => QuadraticLocal.Spill.Raffle.pad (ActualOriginalQLayout.rankCap R u+Fintype.card V*tollQ+1)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "B₀" => budgetR R
local notation "p₀" => max (d₁+1) (d₂+1+padQ)
local notation "A₀" => max (2*C₁) C₂

private theorem min_ratio {x a b : ℝ} (x₀ : 0 ≤ x) (a₀ : 0 < a) (b₀ : 0 < b) :
    min (x/a) (x/b) = x/(max a b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,min_eq_right (div_le_div_of_nonneg_left x₀ a₀ h)]
  · rw [max_eq_left h,min_eq_left (div_le_div_of_nonneg_left x₀ b₀ h)]

private theorem charged {j b N per : ℕ} {k : ℝ} (kp : 0 < k)
    (price : β̂ (j+1) ≤ k*R.family.path.β N per b) {h Ω : ℝ}
    (hp : 1 ≤ h) (hcap : h ≤ (B₀ (j+1))^6) (op : 1 ≤ Ω) (file : Ω ≤ B₀ j)
    (S : Finset V) (w : V → ℝ)
    (birth : ∀v ∈ S,w v =
      (min (free v/((C₁*(β̂ (j+1))^(d₁+1))*Ω)/2)
        (free v/((C₂*(β̂ (j+1))^(d₂+1))*(β̂ (j+1))^padQ)))/h) :
    (∏v ∈ S,free v) ≤ ((B₀ j)^2*(B₀ (j+1))^7)^S.card*
      (A₀*k^p₀*((regulatorRun R.family N per b)⁻¹)^(2*p₀))^S.card*(∏v ∈ S,w v) := by
  let x := β̂ (j+1)
  let y := R.family.path.β N per b
  let a := 2*((C₁*x^(d₁+1))*Ω)
  let c := (C₂*x^(d₂+1))*x^padQ
  have g₁ := (Classical.choose_spec primary).1
  have g₂ := (Classical.choose_spec second).1
  have xgood : 1 ≤ x := (R.alloy.B.a.fits.delayed _).le
  have x₀ : 0 < x := zero_lt_one.trans_le xgood
  have a₀ : 0 < a := by dsimp [a]; positivity
  have c₀ : 0 < c := by dsimp [c]; positivity
  have room : x ≤ k*y := price
  have y₀ : 0 < y := pos_of_mul_pos_right (x₀.trans_le room) kp.le
  have priceA : a ≤ (B₀ j)*(A₀*x^p₀) := by
    calc
      a = Ω*((2*C₁)*x^(d₁+1)) := by dsimp [a]; ring
      _ ≤ _ := mul_le_mul file (mul_le_mul (le_max_left ..)
        (pow_le_pow_right₀ xgood (le_max_left ..)) (pow_nonneg x₀.le _) (by positivity))
        (by positivity) (zero_le_one.trans (budget_pos R))
  have priceC : c ≤ (B₀ j)*(A₀*x^p₀) := by
    calc
      c = C₂*x^(d₂+1+padQ) := by rw [pow_add]; dsimp [c]; ring
      _ ≤ A₀*x^p₀ := mul_le_mul (le_max_right ..)
        (pow_le_pow_right₀ xgood (le_max_right ..)) (pow_nonneg x₀.le _) (by positivity)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (budget_pos R)
  have prefactor : h*max a c ≤ ((B₀ j)^2*(B₀ (j+1))^7) * (A₀*(k*y)^p₀) := by
    calc
      _ ≤ (B₀ (j+1))^6*((B₀ j)*(A₀*x^p₀)) := mul_le_mul hcap (max_le priceA priceC)
        (a₀.le.trans (le_max_left ..)) (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
      _ = ((B₀ j)*(B₀ (j+1))^6)*(A₀*x^p₀) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul (by simpa using (pow_le_pow_right₀ (budget_pos (i:=j) R) (by norm_num:1≤2)))
        (pow_le_pow_right₀ (budget_pos R) (by norm_num:6≤7)) (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
        (pow_nonneg (zero_le_one.trans (budget_pos R)) _))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ x₀.le room _) (by positivity))
        (by positivity) (mul_nonneg (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
          (pow_nonneg (zero_le_one.trans (budget_pos R)) _))
  let total := ((B₀ j)^2*(B₀ (j+1))^7) * (A₀*(k*y)^p₀)
  have atBirth (v:V) (hv:v ∈ S) : free v ≤ total*w v := by
    have weight := birth v hv
    change w v = min (free v/((C₁*x^(d₁+1))*Ω)/2) (free v/c)/h at weight
    rw [div_div,show (C₁*x^(d₁+1)*Ω)*2=a from mul_comm ..,
      min_ratio (freePos v).le a₀ c₀,div_div] at weight
    have positive : 0 < max a c*h := mul_pos (a₀.trans_le (le_max_left ..)) (zero_lt_one.trans_le hp)
    have recover : free v = (h*max a c)*w v := by rw [weight,mul_comm h]; field_simp
    rw [recover]
    exact mul_le_mul_of_nonneg_right prefactor (weight ▸ (div_pos (freePos v) positive).le)
  have power : (k*y)^p₀ = k^p₀*((regulatorRun R.family N per b)⁻¹)^(2*p₀) := by
    change _ = k^p₀*((Real.sqrt y)⁻¹)⁻¹^(2*p₀)
    rw [inv_inv,pow_mul,Real.sq_sqrt y₀.le,mul_pow]
  calc
    _ ≤ ∏v ∈ S,total*w v := prod_le_prod (fun v _=>(freePos v).le) atBirth
    _ = total^S.card*(∏ v ∈ S,w v) := by rw [prod_mul_distrib, prod_const]
    _ = _ := by dsimp only [total]; rw [power,mul_pow]; ring

/-- Apply once to each genuinely born name. Each of the two input prices comes from the
same source order K even when later comparisons ask for larger signed precision. -/
theorem original {j b N per : ℕ} (jb : j < b) (top : b ≤ N) {h Ω : ℝ}
    (hp : 1 ≤ h) (hcap : h ≤ (B₀ (j+1))^6) (op : 1 ≤ Ω) (file : Ω ≤ B₀ j)
    (S : Finset V) (w : V → ℝ)
    (birth : ∀v ∈ S,w v =
      (min (free v/((C₁*(β̂ (j+1))^(d₁+1))*Ω)/2)
        (free v/((C₂*(β̂ (j+1))^(d₂+1))*(β̂ (j+1))^padQ)))/h) :
    (∏v ∈ S,free v) ≤ ((B₀ j)^2*(B₀ (j+1))^7)^S.card*
      (A₀*2^p₀*((regulatorRun R.family N per b)⁻¹)^(2*p₀))^S.card*(∏v ∈ S,w v) := by
  have H := WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le (Nat.succ_le_of_lt jb)
  have β := (R.makes.wilson.represents N per b top).band.1
  change β̂ b/2 ≤ R.family.path.β N per b at β
  exact charged R simple request freshQ u μ extra free D income K freePos warm (by norm_num : (0:ℝ)<2)
    (by linarith only [H,β]) hp hcap op file S w birth

/-- A source born at the upper endpoint uses the next genuine clock, still before either regulator. -/
theorem at_reporter {b N per : ℕ} (top : b ≤ N)
    (calendar : (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b) {h Ω : ℝ}
    (hp : 1 ≤ h) (hcap : h ≤ (B₀ (b+1))^6) (op : 1 ≤ Ω) (file : Ω ≤ B₀ b)
    (S : Finset V) (w : V → ℝ)
    (birth : ∀v ∈ S,w v =
      (min (free v/((C₁*(β̂ (b+1))^(d₁+1))*Ω)/2)
        (free v/((C₂*(β̂ (b+1))^(d₂+1))*(β̂ (b+1))^padQ)))/h) :
    (∏v ∈ S,free v) ≤ ((B₀ b)^2*(B₀ (b+1))^7)^S.card*
      (A₀*4^p₀*((regulatorRun R.family N per b)⁻¹)^(2*p₀))^S.card*(∏v ∈ S,w v) := by
  have H := (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec b calendar
  have β := (R.makes.wilson.represents N per b top).band.1
  change β̂ b/2 ≤ R.family.path.β N per b at β
  exact charged R simple request freshQ u μ extra free D income K freePos warm (by norm_num : (0:ℝ)<4)
    (by linarith only [H,β]) hp hcap op file S w birth

end YM.Integration.WilsonReceivedCloseBirthPrice
