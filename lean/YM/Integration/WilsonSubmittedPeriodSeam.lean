import YM.Integration.WilsonPositionProgramSubmittedQuiet
import YM.Integration.WilsonFiledPeriodSeam

/-! The chronological finite vacuum on the same Wilson ledger and held directions. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSubmittedPeriodSeam
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice


open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDepositedGeometric (source)
open QuadraticLocal.Earn AllOrder.Floe

open WilsonFiledPeriodSeam WilsonCoeffUV.Bank.Realm ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse
open scoped Classical BigOperators

private theorem dimension(n:Side):
    1+(Fintype.card (Woods G n):ℝ)≤(1+(Fintype.card (Hooks G):ℝ))*(n.val:ℝ)^4:=by
  change 1+((Fintype.card (Site n × Hooks G)):ℝ)≤_
  rw [Fintype.card_prod,site_card,Nat.cast_mul,Nat.cast_pow]
  have hn:1≤(n.val:ℝ):=by exact_mod_cast (show 1≤n.val from n.prop)
  nlinarith only [one_le_pow₀ hn (n:=4)]

def tariff (G:Gauge)(i:ℕ):ℝ:=2*((i+2:ℕ):ℝ)*(1+(Fintype.card (Hooks G):ℝ))^(i+2)

def weight (t:ℕ)(j p:ℕ)(x y:Stationary.Link G (coarse R j p)):ℝ:=
  (R.family.side j p).val^(4*(t+2))*
    (1+max ‖flatten (Stationary.arm G _ 1 x)‖ ‖flatten (Stationary.arm G _ 1 y)‖)^(t+2)

def price (i D j p:ℕ):ℝ:=tariff G i*(admittedCost R.family.path.levels j)^D*
  Real.exp (-((R.family.side j p).val:ℝ)/(4*zz R.family.path.levels j))

def Bill (t D j:ℕ):Prop:=∀(N m p e:ℕ)(Z:ℕ→SeriesA G)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),
    Agrees R N m e Z π Γ→m≤j→∀ hj:j < N,
    ∀(F:Forest (step R j p).ratio)(tag:(step R j p).Choices),
    ∀{T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R j p)),
    ∀σ C s A,Issued R N (j+1) e (Z (j+1)) σ C→Issued R N j e (Z j) s A→t≤e+2→
    ∀x y:Stationary.Link G (coarse R j p),
    let current:=QuadraticLocal.Fk.grant (π (j+1)) (Step.tape (e+2)) Q
    let program:=(RunFormalChain.fromRun R).step N j p hj
    let field:=fun z:Stationary.Link G (coarse R j p)=>Stationary.arm G _ 1 z
    let fromLower:=fun z=>WilsonFiledPeriodSeam.filed R N j (coarse R j p) (Z j) t (e+2) (flatten (field z))
    ‖(Symmetry.Orbit.ground program F tag current (e+2) t (field x)
      -Symmetry.Orbit.ground program F tag current (e+2) t (field y))
      +((fromLower x-fromLower y:ℝ):ℂ)‖≤price R t D j p*weight R t j p x y

theorem at_date (R:Run G)(t D j:ℕ)(simple:G.Simple)(invoice:WilsonFiledPeriodSeam.Direction R t D j):
    Bill R t D j:=by
  intro N m p e Z π Γ aligned lower hj F tag T dec fin J Q σ C s A above below cap x y current program field returned
  let n:=coarse R j p
  let X:=flatten (field x)
  let Y:=flatten (field y)
  let w:=1+max ‖X‖ ‖Y‖
  have w1:1≤w:=by dsimp only [w]; linarith only [norm_nonneg X,le_max_left ‖X‖ ‖Y‖]
  have top(out:Stationary.Link G n)(b:‖flatten (field out)‖≤ max  ‖X‖ ‖Y‖)(u):
      |flatten (field out) u|≤w:=by
    have h:=norm_le_pi_norm (flatten (field out)) u
    change |flatten (field out) u|≤‖flatten (field out)‖ at h
    exact (h.trans b).trans (by dsimp only [w]; linarith)
  have first:=invoice N p hj e (Z j) s A below cap X Y w w1
    (top x (le_max_left ..)) (top y (le_max_right ..))
  let finite:=diff (output R N j p) t X Y
  let cover:=returned x-returned y
  change |finite-cover|≤_ at first
  have exactOutput:=WilsonPositionProgramSubmittedQuiet.original R Z π Γ aligned lower hj F tag Q simple above x y t cap
  change _ = -(finite:ℂ) at exactOutput
  change ‖_+((cover:ℝ):ℂ)‖≤_
  rw [exactOutput]
  have factor:-(finite:ℂ)+(cover:ℂ)=-((finite-cover:ℝ):ℂ):=by push_cast; ring
  rw [factor,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  apply first.trans
  have sizes:((1+(Fintype.card (Woods G n):ℝ))*w)^(t+2)≤
      (((1+(Fintype.card (Hooks G):ℝ))*(n.val:ℝ)^4)*w)^(t+2):=
    pow_le_pow_left₀ (mul_nonneg (by positivity) (by linarith only [w1]))
      (mul_le_mul_of_nonneg_right (dimension n) (by linarith only [w1])) _
  have hfee:=pow_nonneg (zero_le_one.trans (admittedCost_one R.family.path.levels j)) D
  have grow:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sizes
    (show 0≤2*((t+2:ℕ):ℝ) by positivity))
    (mul_nonneg hfee (Real.exp_nonneg (-(n.val:ℝ)/(4*zz R.family.path.levels j))))
  refine grow.trans_eq ?_
  dsimp only [price,tariff,weight,field,n,w,X,Y]
  simp only [mul_pow,pow_mul]
  ring

/-- The chronological pupil and the elected lower vacuum on one actual finite
forest. Its price precedes the UV bound and period, also for moving tests. -/
theorem original (G:Gauge)(t:ℕ):∃v:ℕ→Gear G→ℝ,∃D:ℕ,∀(R:Run G),G.Simple→
    RG05Preconstruction.ReadoutPurchase R.b→FundedMarkedCoverRows.prices v R.kit→
    ∀ᶠj:ℕ in atTop,Bill R t D j:=by
  obtain ⟨v,D,estimate⟩:=WilsonFiledPeriodSeam.original G t
  refine ⟨v,D,?_⟩
  intro R simple reading paid
  filter_upwards [estimate R simple reading paid] with j invoice
  exact at_date R t D j simple invoice

end YM.Integration.WilsonSubmittedPeriodSeam
end
