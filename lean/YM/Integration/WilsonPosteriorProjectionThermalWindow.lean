import YM.Integration.WilsonConditionalTaylorCalendar
import YM.Next.RANK.NoSpill
import YM.Extra.ITERATION_NO_LOSS.Post
import YM.Next.MULTISOURCE.Wage

/-! The actual coarse reporting amplitude is the historical monitor times
the coarse coupling. A numerical presale for the change of nominal inverse
coupling keeps the fine thermal coordinate in the same eventual interval.
The remaining monitor costs less than every preassigned positive power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionThermalWindow

open Set Function Filter Finset Lattice Wilson RG Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato WilsonConditionalTaylorThreshold WilsonConditionalTaylorCalendar
open scoped Classical Topology BigOperators
variable {G : Gauge}

def changeFee (G : Gauge) : Fare := fun _ _ P _ => 2*|G.slopeConstant*Real.log P.L|

theorem interval (R : Run G) (j n : ℕ)
    (paid : changeFee G (R.family.path.levels.params j) (R.family.path.levels.params (j+1))
      (R.family.path.levels.clock.op j n).patch (R.family.path.levels.clock.op j n).kernel ≤
      R.family.path.levels.clock.hatBeta j) :
    let x := R.family.path.levels.clock.hatBeta j
    let y := R.family.path.levels.clock.hatBeta (j+1)
    x/2 ≤ y ∧ y ≤ 2*x := by
  intro x y
  let inc := G.slopeConstant*Real.log (R.family.path.levels.clock.op j n).patch.L
  have step : y=x+inc := Extra.Iteration.block_beta (a:=R.family.path.levels) j
  have budget : 2*|inc| ≤ x := paid
  rw [step]
  constructor <;> linarith only [budget,le_abs_self inc,neg_le_abs inc]

theorem fee (K : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ, x/4 ≤ β → β ≤ 4*x →
      let g := (Real.sqrt β)⁻¹
      let θ := (Real.sqrt x)⁻¹*Real.exp ((Real.log (Real.log x))^2)
      (max 1 (g⁻¹*θ))^K ≤ g^(-δ) := by
  have h₈ : 0<δ/8 := by positivity
  filter_upwards [eventually_ge_atTop (16:ℝ),Next.Rank.Paint.monitors (K:ℝ) (δ/8) h₈,
    (tendsto_rpow_atTop h₈).eventually_ge_atTop ((2:ℝ)^K)] with x big monitor constant β low high g θ
  let M := Real.exp ((Real.log (Real.log x))^2)
  have hx : 0<x := by linarith only [big]
  have beta : 0<β := by linarith only [low,big]
  have pos : 0<M := Real.exp_pos _
  have M1 : 1≤M := Real.one_le_exp (sq_nonneg _)
  have slow : M^K ≤ x^(δ/8) := by
    rw [Real.rpow_def_of_pos hx,show M^K=Real.exp ((K:ℝ)*(Real.log (Real.log x))^2) from
      (Real.exp_nat_mul _ K).symm]
    exact Real.exp_le_exp.mpr (monitor.trans_eq (mul_comm ..))
  have sqrt4 : Real.sqrt (4*x)=2*Real.sqrt x := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)];norm_num
  have fraction : Real.sqrt β*(Real.sqrt x)⁻¹ ≤ 2 := by
    rw [←div_eq_mul_inv]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mpr ((Real.sqrt_le_sqrt high).trans_eq sqrt4)
  have ratio : max 1 (g⁻¹*θ) ≤ 2*M := by
    change max 1 (((Real.sqrt β)⁻¹)⁻¹*((Real.sqrt x)⁻¹*M)) ≤ 2*M
    rw [inv_inv,←mul_assoc]
    exact max_le (by linarith only [M1]) (mul_le_mul_of_nonneg_right fraction pos.le)
  have shallow : Real.sqrt x ≤ β := by
    apply le_trans _ low
    apply (Real.sqrt_le_left (by positivity : 0≤x/4)).mpr
    nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr big)]
  calc
    _ ≤ (2*M)^K := pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) ratio _
    _ = 2^K*M^K := mul_pow _ _ K
    _ ≤ x^(δ/8)*x^(δ/8) := mul_le_mul constant slow (pow_nonneg pos.le _) (Real.rpow_nonneg hx.le _)
    _ = (Real.sqrt x)^(δ/2) := by
      rw [←Real.rpow_add hx,Real.sqrt_eq_rpow,←Real.rpow_mul hx.le]; congr 1; ring
    _ ≤ β^(δ/2) := Real.rpow_le_rpow (Real.sqrt_nonneg _) shallow (half_pos hδ).le
    _ = g^(-δ) := by
      change _=((Real.sqrt β)⁻¹)^(-δ)
      rw [Real.inv_rpow (Real.sqrt_nonneg _),Real.rpow_neg (Real.sqrt_nonneg _),inv_inv,
        Real.sqrt_eq_rpow,←Real.rpow_mul beta.le]
      congr 1
      ring

/-- Fee in the *actual reported coarse representation* and the fine
representation's own inverse-temperature coupling, uniformly for all
later stages and all enclosing volume parameters. -/
theorem reported (R : Run G) (simple : G.Simple) (K : ℕ) {δ : ℝ} (hδ : 0<δ)
    (booked : ∀ᶠ j : ℕ in atTop, ∀ n, changeFee G (R.family.path.levels.params j)
      (R.family.path.levels.params (j+1)) (R.family.path.levels.clock.op j n).patch
      (R.family.path.levels.clock.op j n).kernel ≤ R.family.path.levels.clock.hatBeta j) :
    ∀ᶠ k : ℕ in atTop, ∀ j, k≤j → ∀ N n, j<N →
      let β := (R.family.path.rep N n (j+1)).beta
      let g := (Real.sqrt β)⁻¹
      let θ := (R.family.path.rep N n j).p.threshold
      0<g ∧ (max 1 (g⁻¹*θ))^K ≤ g^(-δ) := by
  obtain ⟨t,rate⟩ := eventually_atTop.mp ((Multi.Wage.hat_tend simple R.family.path.levels).eventually (fee K hδ))
  obtain ⟨j₀,sees⟩ := eventually_atTop.mp booked
  filter_upwards [eventually_ge_atTop t,eventually_ge_atTop j₀] with k mature late j kj N n jN β g θ
  obtain ⟨lo,hi⟩ := interval R j n (sees j (late.trans kj) n)
  obtain ⟨βlo,βhi⟩ := (R.T.choice.represents N n (j+1) jN).band
  let x := R.family.path.levels.clock.hatBeta j
  let y := R.family.path.levels.clock.hatBeta (j+1)
  change x/2≤y at lo
  change y≤2*x at hi
  change y/2≤β at βlo
  change β≤2*y at βhi
  have lower : x/4 ≤ β := by linarith only [lo,βlo]
  have upper : β ≤ 4*x := by linarith only [hi,βhi]
  have x1 : 1<x := R.family.path.levels.fits.delayed j
  have positive : 0<β := by linarith only [x1,lower]
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr positive),?_⟩
  change (max 1 (g⁻¹*(R.family.path.rep N n j).p.threshold))^K ≤ _
  have vac : (R.family.path.rep N n j).p=R.family.path.levels.budget j := (R.T.choice.represents N n j jN.le).vac
  rw [vac]
  exact rate j (mature.trans kj) β lower upper

end YM.Integration.WilsonPosteriorProjectionThermalWindow
end

