import YM.Integration.WilsonThermometerUnitFilingCoverPayroll
import YM.Integration.WilsonThermometerCenteredRadius

/-! Restore the funded captured markQ on the true reporting coupling at one exponent for every finite subroster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverCurrency
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonThermometerUnitFilingMomentPanel WilsonOriginalRelativeMixedFields
open RegulatorIR RegulatorIR.Taping RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Halo RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open scoped Classical BigOperators ENNReal
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
local notation "β" => R.alloy.B.a.clock.hatBeta (i+1)


variable {W:Type}{years:W→ℕ}{sizes:Page years→Side}{L:Heir sizes G}
    (T:L.Accounts){h:ℕ}(group:W→Portrait G)(law:∀ x,LocalStamp (group x) h)
    (v:W)(rows:Finset F.modelIndex)(t:Wallet actors)(a:ℂ→L[ℝ]ℝ)
    (deposit:group v=WilsonThermometerUnitFilingCoverAudition.bank F.model rows t a)
local notation "output"=> (WilsonThermometerUnitFilingCoverStock.report T group law).main (Page.opening years v)
local notation "marks" l "at" ρ "on" pr "to" u =>
  ((Premium.rooted (Budget.Tariff.native ρ pr u) 0).uses (WilsonThermometerUnitFilingCoverRoom.plot (G:=G) l))


def part (G:Gauge)(h u e:ℕ):ℝ:=
  (3+8*((e+h:ℕ):ℝ))^u*WilsonThermometerUnitFilingMomentSale.price G (e+h) u 1

def gross (G:Gauge)(h u accuracy:ℕ):ℝ:=
  ∑ e∈Finset.range (accuracy+1),part G h u e

theorem sign {G:Gauge}(h u e:ℕ):0≤part G h u e:=by
  unfold part WilsonThermometerUnitFilingMomentSale.price WilsonThermometerUnitFilingMomentSale.positionCost
  have f0:=WilsonOriginalSuspendedTensor.nonnegative G one_pos (e+h)
  positivity

private theorem scale {a bound y g cash:ℝ}(gp:0<g)(cash0:0≤cash)(A:0≤a)(B:a≤bound)
    (paid:y*g^2≤2)(top:ℕ): a*y*(1+cash)/g^top ≤ 2*bound*(1+cash)/g^(top+2):=by
  apply (le_div_iff₀ (pow_pos gp _)).mpr
  calc
    _ = a*(1+cash)*(y*g^2):=by rw [pow_add];field_simp
    _ ≤ a*(1+cash)*2:=mul_le_mul_of_nonneg_left paid (mul_nonneg A (by linarith))
    _ ≤ _:=by nlinarith [mul_le_mul_of_nonneg_right B (show 0≤1+cash by linarith)]

local notation "g"=>Coat.gStep (R.family.path.rep N per (i+1)).beta

include deposit in
theorem original (simple:G.Simple)(purchased:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (live:i+1≤N)(late:Real.exp 1≤β)(gp:0<g)(soft:g≤1){Ω fee cash:ℝ}(cash0:0≤cash)(top:ℕ)
    (low:F.cost≤1)(small:F.cost≤Ω⁻¹)(issued:(F.w ())⁻¹=max 1 Ω*(1+fee))(limit:fee*g^top≤cash)
    (re:‖a‖≤1){l ρ:ℝ}(hl:0<l)(hr:0<ρ)(safe:l≤ρ)(accuracy e r u:ℕ)(wanted:e≤accuracy):
    markQ (marks l at ρ on hr to u) ((output) e r) ≤ ENNReal.ofReal
      (2*gross G h u accuracy*(1+cash)/g^(top+2)):=by
  have annual:=WilsonThermometerUnitFilingCoverPayroll.earned R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i floor F T group law v rows t a deposit simple purchased late one_pos gp soft top
    low small issued limit re hl hr safe e r u
  apply annual.trans
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_one]
  apply scale gp cash0 (sign h u e) _ (WilsonThermometerCenteredRadius.temperature R N per (i+1) live) top
  exact Finset.single_le_sum (fun j _=>sign h u j) (Finset.mem_range.mpr (by omega))

end YM.Integration.WilsonThermometerUnitFilingCoverCurrency
