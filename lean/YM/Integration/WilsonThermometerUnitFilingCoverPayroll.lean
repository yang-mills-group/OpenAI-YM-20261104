import YM.Integration.WilsonThermometerUnitFilingCoverShare
import YM.Integration.WilsonThermometerUnitFilingPositiveWage

/-! The placed independent pupil's actual return at the captured cover page. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverPayroll
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

include hk floor deposit in
theorem original (simple:G.Simple)(purchased:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (late:Real.exp 1≤β){δ:ℝ}(tiny:0<δ)(re:‖a‖≤1)
    {l ρ:ℝ}(hl:0<l)(hr:0<ρ)(safe:l≤ρ)(e r u:ℕ):
    markQ (marks l at ρ on hr to u) ((output) e r) ≤
      ENNReal.ofReal (WilsonThermometerUnitFilingCoverInvoice.invoice G (e+h) u δ β F.cost (F.w ())):=by
  exact WilsonThermometerUnitFilingCoverShare.original F.model rows t a T group law v deposit F.salary
    (Poetry.Agenda.stem ..) tiny late
    (WilsonThermometerUnitFilingPositiveWage.aperture R hk D i floor simple purchased) (F.salary.positive ()) re hl hr safe e r u

private theorem restore {A C w g fee cash:ℝ}(pos:0≤A)(gp:0<g)(soft:g≤1)(top:ℕ)
    (cost:C/w≤1+fee)(priced:fee*g^top≤cash): A*C/w≤A*(1+cash)/g^top:=by
  apply (le_div_iff₀ (pow_pos gp top)).mpr
  calc
    (A*C/w)*g^top = A*((C/w)*g^top):=by ring
    _ ≤ A*((1+fee)*g^top):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cost (pow_nonneg gp.le _)) pos
    _ ≤ _:=mul_le_mul_of_nonneg_left (by rw [add_mul,one_mul];linarith [pow_le_one₀ gp.le soft (n:=top)]) pos

include deposit in
theorem earned (simple:G.Simple)(purchased:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
    (late:Real.exp 1≤β){δ g Ω fee cash:ℝ}(tiny:0<δ)(gp:0<g)(soft:g≤1)(top:ℕ)
    (low:F.cost≤1)(small:F.cost≤Ω⁻¹)(issued:(F.w ())⁻¹=max 1 Ω*(1+fee))(limit:fee*g^top≤cash)
    (re:‖a‖≤1){l ρ:ℝ}(hl:0<l)(hr:0<ρ)(safe:l≤ρ)(e r u:ℕ):
    markQ (marks l at ρ on hr to u) ((output) e r) ≤ ENNReal.ofReal
      ((3+8*((e+h:ℕ):ℝ))^u*WilsonThermometerUnitFilingMomentSale.price G (e+h) u δ*β^δ*(1+cash)/g^top):=by
  apply (original R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor F T group law v rows t a deposit
    simple purchased late tiny re hl hr safe e r u).trans
  apply ENNReal.ofReal_le_ofReal
  have fee' := WilsonThermometerUnitFilingPositiveWage.quote (F.salary.positive ()) low small issued
  have wage : 0≤WilsonThermometerUnitFilingMomentSale.price G (e+h) u δ:=by
    unfold WilsonThermometerUnitFilingMomentSale.price WilsonThermometerUnitFilingMomentSale.positionCost
    have f0:=WilsonOriginalSuspendedTensor.nonnegative G one_pos (e+h)
    positivity
  exact restore (mul_nonneg (mul_nonneg (by positivity) wage) (Real.rpow_nonneg ((Real.exp_pos 1).le.trans late) _))
    gp soft top fee' limit

end YM.Integration.WilsonThermometerUnitFilingCoverPayroll
