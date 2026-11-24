import YM.Integration.WilsonReceivedCloseStamp
import YM.Integration.WilsonReceivedFirstPrepaidReading

/-! The restored old salary is paid on the same measured continuation as the newly filed row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFirstQEconomy
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Stationary Comparison.RG02 QuadraticLocal.Rebirth ConnectedActivityE6 Pressure
open QuadraticLocal.Affinity
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (hi : m  ≤  i) (cut : i < N)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson : Lesson (N:=N) R hk D Q π Γ hi)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V ι : Type} [Fintype V] [DecidableEq V] {X : V → Type} [Countable ι]
  {passport : Earn.Passport (R.family.side (i+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row passport (Stock.census V) G (Affinity.Wallet actors))
  (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J i))

local notation "siz" => (R.alloy.B.a.S.oneStep i per).exact_size
local notation "sp" => (Pane.panel R.alloy i siz).ratio.count
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "rebate" => Oak.rebate R hk D Q π Γ hi op lesson

local notation "y" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "xβ" => R.alloy.B.a.clock.hatBeta i
local notation "e" => (y)^(-(order:ℝ))
local notation "vac" => Burn.young y k
local notation "g₀" => Coat.gStep (Ψ (i+1)).beta
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "b" => (Ω)⁻¹
local notation "cost" => (fig).produce sp*b
local notation "spent" => (fig).hitPrice G sp (Ψ (i+1)).p (Ψ i).p b e vac g₀
local notation "fee" => QuadraticLocal.Earn.Invoice.price (Ψ i).p (fig).mist (order+shelf+1) op.count ((Ψ i).p.supportExponent+1+1) (fig).limitC G
local notation "bill" => (fig).fidelity*fee*(cost)+spent

include course cut voter in
theorem original (scroll:VowsR.LawScroll G φ) (employed:VowsR.Chamber scroll R.kit D Q books)
    (month:Rebirth.Scholar.Month R.rolls D Q R.alloy.delay) (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (rank:order ≤ Burn.horizon k+1) (narrow:shelf ≤ R.alloy.B.a.clock.J i) (load:op.count ≤ Burn.horizon k+2)
    (simple:G.Simple) (prec:ℕ) (deep:2*prec+8 ≤ order) (aged:prec+3 ≤ 3*k+2) {κ:ℝ} (kp:0<κ)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple prec order k deep aged kp ≤ i)
    (upperCap:Ω ≤ y) (cool:gf ≤ 1) :
    rebate*cost ≤ y ∧ ∀h:ℝ, h ≤ max (max 1 (bill)) ((Ω)^5+1) → h ≤ (10+κ)*(y)^5:=by
  have rich:4 ≤ Ω:=MintClock.Page.roofers ..
  have b₀:0 ≤ b:=inv_nonneg.mpr (by linarith)
  have hot:1 ≤ y:=(R.alloy.B.a.fits.delayed _).le
  have yp:0<y:=zero_lt_one.trans_le hot
  have epos:0 ≤ e:=Real.rpow_nonneg yp.le _
  have ecap:e ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos hot (neg_nonpos.mpr (by positivity))
  have stamp:=WilsonReceivedCloseStamp.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M order shelf voter scroll employed month pass hospital rank narrow load b₀ le_rfl
  have lower:=WilsonReceivedMeasuredStampPrice.original R hk D Q π Γ Ψ course books hi cut op lesson ahead
    actors M order shelf voter pass hospital narrow load simple prec deep aged kp late b₀ le_rfl epos
  have envelope:budgetR R i ≤ y:=(min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le hot
    (show Beaming.grain (R.alloy.B.a.clock.J i) ≤ 1 by unfold Beaming.grain;apply (div_le_one (by positivity)).2; simp)).trans_eq (Real.rpow_one _))
  refine ⟨stamp.trans envelope,fun h bound=>bound.trans ?_⟩
  have degree:y ≤ (y)^5:=(pow_one (y)).symm.le.trans (pow_le_pow_right₀ hot (by norm_num))
  have old:8*(Ω)*e ≤ 8*(y)^5:=(mul_le_of_le_one_right (by linarith:0 ≤ 8*(Ω)) ecap).trans
    (mul_le_mul_of_nonneg_left (upperCap.trans degree) (by norm_num))
  have u:0 ≤ gf:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have model:κ*(gf)^prec ≤ κ*(y)^5:=mul_le_mul_of_nonneg_left
    ((pow_le_one₀ u cool).trans (one_le_pow₀ hot)) kp.le
  have released:(Ω)^5 ≤ (y)^5:=pow_le_pow_left₀ (by linarith) upperCap _
  have one:1 ≤ (y)^5:=one_le_pow₀ hot
  refine max_le (max_le ?_ (lower.trans ((add_le_add old model).trans ?_))) ?_
  · nlinarith only [one,mul_nonneg kp.le (zero_le_one.trans one)]
  · nlinarith only [one]
  · nlinarith only [one,released,mul_nonneg kp.le (zero_le_one.trans one)]

theorem physical {G:Gauge} (R:Run G) (simple:G.Simple) :
    ∀ᶠ j:ℕ in atTop, ∀N per:ℕ,j+1<N →
      let g:=Coat.gStep (R.family.path.rep N per (j+1)).beta
      let g':=Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta
      g ≤ 1 ∧ g' ≤ 1 ∧ R.alloy.B.a.clock.hatBeta ((j+1)+1)*g^2 ≤ 4:=by
  have ratio:=RG01.Physical.nextHat simple R.alloy.B.a
  have next:Tendsto (fun j:ℕ=>j+1) atTop atTop:=tendsto_add_atTop_nat 1
  have cool:=WilsonRootedObservedRate.power R simple 0 0 le_rfl (show 0<(1:ℝ) by norm_num)
  filter_upwards [cool,next.eventually cool,next.eventually ratio] with j chilled still rate N per cut g g'
  have first:(2*g)^(0+1) ≤ 1*g^0:=chilled N per (by omega)
  have second:(2*g')^(0+1) ≤ 1*g'^0:=still N per cut
  simp only [Nat.zero_add,pow_one,pow_zero,mul_one] at first second
  refine ⟨by linarith,by linarith,?_⟩
  let β:=(R.family.path.rep N per (j+1)).beta
  have band:R.alloy.B.a.clock.hatBeta (j+1)/2 ≤ β:=(R.makes.wilson.represents N per (j+1) cut.le).band.1
  have pos:0<β:=(half_pos (zero_lt_one.trans (R.alloy.B.a.fits.delayed _))).trans_le band
  change R.alloy.B.a.clock.hatBeta ((j+1)+1)*(Real.sqrt β)⁻¹^2 ≤ 4
  rw [inv_pow,Real.sq_sqrt pos.le,←div_eq_mul_inv,div_le_iff₀ pos]
  change R.alloy.B.a.clock.hatBeta ((j+1)+1) ≤ 2*R.alloy.B.a.clock.hatBeta (j+1) at rate
  linarith

end YM.Integration.WilsonReceivedFirstQEconomy
