import YM.Integration.WilsonReceivedCloseStationedFaces


/-! One activation date for the signed three-source physical window before all tori and positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseStationCalendar
open Lattice RG Wilson Marker Org AllOrder AllOrder.Floe AllOrder.Floe.Step PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato QuadraticLocal Filter
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
  (D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ:ℕ→ℕ)
  (protection:∀ x k:ℕ,k≤x→∀β:ℝ,R.alloy.delay.betaEntry x≤β→
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2)≤β)
  {V:Type} [Fintype V] [DecidableEq V] (grades:V→ℕ) (k order shelf seats a d q prec span degree:ℕ) (u H angleCap cap ε:ℝ) (u1:1≤u)
  (deep:2*(prec+1)+8≤ order) (aged:prec+4≤3*k+2)
  (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
private theorem enoughRaw {p r:ℕ} (bound:2*(p+1)+8≤r) : 2*p+8≤r := by omega
private theorem enoughAge {p k:ℕ} (bound:p+4≤3*k+2) : p+3≤3*k+2 := by omega
local notation "pages" => WilsonReceivedCloseSlate.opens R D grades order shelf seats simple protection
  prec span deep aged H angleCap hp zero_lt_one
local notation "stamp" => WilsonReceivedMeasuredStampPrice.opening R simple prec order k (enoughRaw deep) (enoughAge aged) zero_lt_one
local notation "paid" => WilsonReceivedCloseSignedPrice.opening R simple degree a prec seats cp
  (η:=1) zero_lt_one (ε:=1) zero_le_one
local notation "budget" => WilsonReceivedCloseEndpoint.with_history R simple degree (2*2) 0 cp (η:=1)
  zero_lt_one (le_rfl:0≤(0:ℝ))
local notation "clock" => WilsonReceivedCloseChainFunding.upper R simple degree cap
local notation "selected" => WilsonReceivedLogWindow.original R simple D φ protection grades order shelf
  k seats span H angleCap hp
local notation "earn" => WilsonReceivedCloseSourceCalendar.reporter_fee R simple
  (WilsonReceivedCloseStationedGrade.nonneg u1 (zero_le_one:0≤(1:ℝ)) a prec) zero_lt_one
local notation "tested" => WilsonReceivedCloseSourceCalendar.reporter_fee R simple
  (WilsonReceivedCloseOrdinaryGrade.nonneg (Stock.census V) a (2*d+1) q (zero_le_one.trans u1)) ep

def Ready (m b:ℕ) : Prop :=
    (eventually_atTop.mp (pages)).choose ≤ m ∧ stamp ≤ m+1 ∧ paid ≤ b ∧
    (eventually_atTop.mp (budget)).choose ≤ b ∧ (eventually_atTop.mp (clock)).choose ≤ b ∧
    (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ b ∧
    (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose ≤ b ∧
    (eventually_atTop.mp (selected)).choose ≤ m ∧ (eventually_atTop.mp (earn)).choose ≤ b ∧
    (eventually_atTop.mp (tested)).choose ≤ b

theorem original : ∀ᶠ m:ℕ in atTop, ∀ b, m≤b →
    Ready R simple D φ protection grades k order shelf seats a d q prec span degree u H angleCap cap ε u1 deep aged hp cp ep m b := by
  filter_upwards [eventually_ge_atTop (eventually_atTop.mp (pages)).choose,
    eventually_ge_atTop (stamp),eventually_ge_atTop (paid),
    eventually_ge_atTop (eventually_atTop.mp (budget)).choose,
    eventually_ge_atTop (eventually_atTop.mp (clock)).choose,
    eventually_ge_atTop (eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose,
    eventually_ge_atTop (eventually_atTop.mp (WilsonReceivedClosePhysicalBirths.cool R simple)).choose,
    eventually_ge_atTop (eventually_atTop.mp (selected)).choose,
    eventually_ge_atTop (eventually_atTop.mp (earn)).choose,
    eventually_ge_atTop (eventually_atTop.mp (tested)).choose] with m h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  intro b mb
  exact ⟨h₁,h₂.trans (Nat.le_succ m),h₃.trans mb,h₄.trans mb,h₅.trans mb,h₆.trans mb,h₇.trans mb,
    h₈,h₉.trans mb,h₁₀.trans mb⟩

end YM.Integration.WilsonReceivedCloseStationCalendar
