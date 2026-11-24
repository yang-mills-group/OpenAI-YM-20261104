import YM.Integration.WilsonThermometerUnitFilingMomentPanel
import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonPhysicalHistoryPriorAperture
/-! Positive angular moment income of the actual one-color Wilson appointment.
It holds for the particular pupil paid on the auxiliary school with the
complete three-field compound, as well as each genuine later replant. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPositiveWage
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonThermometerUnitFilingMomentPanel WilsonOriginalRelativeMixedFields
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {m N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(ahead:Mentor.Forecast D R.rolls Q φ books)
  {X:Unit → Type} [∀v,AddCommGroup (X v)] [∀v,Module ℝ (X v)]
  (actors:∀v,Set (X v))(pieces:∀v,Submodule ℝ (X v))(grades:Unit → ℕ)
  (order shelf seats i:ℕ)(floor:m ≤ i)
  {physical:Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census Unit)}
  (F:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor physical)
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "β" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "S" => (Stock.census Unit).fire ()
local notation "sides" => R.family.side (i+1) per

include hk floor in
theorem aperture (simple:G.Simple)(paid:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay):
    Real.exp ((σ)⁻¹^2) ≤ β:=by
  apply paid (R.alloy.B.a.clock.J (i+1)) k
  · exact (show k ≤ Burn.horizon k+2 by unfold Burn.horizon;omega).trans
      (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ i))))
  · exact (R.alloy.B.valid.pays i).trans (Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ i))

theorem quote {c w Ω fare:ℝ}(wc:0<w)(low:c ≤ 1)(small:c ≤ Ω⁻¹)
    (issued:w⁻¹=max 1 Ω*(1+fare)) : c/w ≤ 1+fare:=by
  have ap:0 < max 1 Ω:=one_pos.trans_le (le_max_left ..)
  have wage:0 ≤ 1+fare:=le_of_lt (pos_of_mul_pos_right (issued ▸ inv_pos.mpr wc) ap.le)
  have cancel:c*max 1 Ω ≤ 1:=by
    rcases le_total Ω 1 with h|h
    · simpa only [max_eq_left h,mul_one] using low
    · have op:0<Ω:=one_pos.trans_le h
      rw [max_eq_right h]
      calc
        _ ≤ Ω⁻¹*Ω:=mul_le_mul_of_nonneg_right small op.le
        _ = _:=inv_mul_cancel₀ op.ne'
  calc
    _ = c*max 1 Ω*(1+fare):=by rw [div_eq_mul_inv,issued,mul_assoc]
    _ ≤ 1*(1+fare) :=mul_le_mul_of_nonneg_right cancel wage
    _ = _:=one_mul _

theorem original (simple:G.Simple)(paid:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (late:Real.exp 1 ≤ β){δ:ℝ}(tiny:0<δ){l:Side}(h:(sides).val∣l.val)
    (t:Wallet actors)(x:Site l)(j r a:ℕ)(cells:Finset (Choice (S).val sides l G r)):
    (∑u∈cells,payment h F.model t S x j r a u) ≤
      WilsonThermometerUnitFilingMomentSale.price G r a δ * β^δ*(F.cost/F.w ()):=by
  have root:=aperture R hk D i floor simple paid
  have billed:=WilsonThermometerUnitFilingMomentPanel.original h F.model F.salary (Poetry.Agenda.stem ..)
    tiny late root t S x j r a cells
  simp only [Poly.toll,Census.fire,prod_singleton] at billed
  rw [←mul_div_assoc,le_div_iff₀ (F.salary.positive ()),mul_comm _ (F.w ())]
  exact billed

theorem funded (simple:G.Simple)(paid:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (late:Real.exp 1 ≤ β){δ g Ω fare cash:ℝ}(tiny:0<δ)(gp:0<g)(soft:g ≤ 1)(top:ℕ)
    (low:F.cost ≤ 1)(small:F.cost ≤ Ω⁻¹)(issued:(F.w ())⁻¹=max 1 Ω*(1+fare))(limit:fare*g^top ≤ cash)
    {l:Side}(h:(sides).val∣l.val)(t:Wallet actors)(x:Site l)(j r a:ℕ)(cells:Finset (Choice (S).val sides l G r)):
    g^top * (∑u∈cells,payment h F.model t S x j r a u) ≤
      WilsonThermometerUnitFilingMomentSale.price G r a δ * β^δ*(1+cash):=by
  let A:=WilsonThermometerUnitFilingMomentSale.price G r a δ*β^δ
  have here:=original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor F simple paid late tiny h t x j r a cells
  have net:=quote (F.salary.positive ()) low small issued
  have positive:0 ≤ WilsonThermometerUnitFilingMomentSale.price G r a δ:=by
    unfold WilsonThermometerUnitFilingMomentSale.price WilsonThermometerUnitFilingMomentSale.positionCost
    have f0:=WilsonOriginalSuspendedTensor.nonnegative G one_pos r
    positivity
  have ap:0 ≤ A:=mul_nonneg positive (Real.rpow_nonneg ((Real.exp_pos 1).le.trans late) _)
  have reduction:g^top ≤ 1:=pow_le_one₀ gp.le soft
  calc
    _ ≤ g^top*(A*(F.cost/F.w ())):=mul_le_mul_of_nonneg_left here (pow_nonneg gp.le _)
    _ = A*((F.cost/F.w ())*g^top):=by ring
    _ ≤ A*((1+fare)*g^top):=by gcongr
    _ ≤ A*(1+cash):=mul_le_mul_of_nonneg_left (by rw [add_mul,one_mul];exact add_le_add reduction limit) ap

end YM.Integration.WilsonThermometerUnitFilingPositiveWage
