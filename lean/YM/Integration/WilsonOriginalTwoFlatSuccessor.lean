import YM.Integration.WilsonOriginalFiledSuccessorIncome
import YM.Integration.WilsonOriginalTwoFlatDated

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatSuccessor
open Filter MeasureTheory Multi
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors AnalyticBridge.SectorAffine.Offset
open MeasureTheory Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m   ≤   i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter

local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "lamps" => rendered student (Ψ i).p oldG
local notation "gauge" => Tint.Patrol.report student P.output oldG
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "cash" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G*
  ((fig).produce (sheet).ratio.count*P.cost)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "marks" => Stock.census V

open WilsonRootedKioskOccupiedSlip WilsonOriginalFlatFiledMask


open WilsonOriginalOrdinaryFlatHulls WilsonCapturedPrimarySoftPartition
open WilsonThermometerUnitFilingCoarse WilsonOriginalFlatOccupiedRate WilsonOriginalFlatFiledMask
open WilsonReceivedQuietCrownOwner OPE.Therm
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "β" => R.alloy.B.a.clock.hatBeta i

private abbrev rowsOf {G : Gauge} {n : Side} {V X I : Type} [DecidableEq V] {o : V→Site n} {p : BudgetPoint}
    {U : Census V} (_ : Lamps X I G p o U) := I

open WilsonOriginalOccupiedCorridor WilsonOriginalOccupiedStencil
open private weaker from YM.Integration.WilsonOriginalOccupiedCorridor

include cut in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (ticket:TicketP R.alloy R.kit D Q){u v b:ℕ}(floor:m ≤ u)(uv:u ≤ v)(vb:v ≤ b)(bc : b < i)
    (fixed:WilsonSingleHardRadius.first R simple ≤ u)(capture:WilsonCenteredCaptureClock.first R simple ≤ b)
    (pole q:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged ep ≤ i)
    (x:Wallet actors)(s:(marks).Mode)(n:ℕ)(np:0<n)
    (stage:∀l,b ≤ l → n ≤ R.alloy.B.a.clock.J l)(load_ok:∀t:(marks).Mode,t.val.card ≤ n)
    (cap:∀l,b ≤ l → LocalComparison.forcedDivisor R.family l ≤ 1)
    (tiny:WilsonOriginalOccupiedWallet.inverseAmplitude n κ ≤ 1)
    (Z:Support (R.family.side b per))(center:Site (R.family.side b per))(home:center∈Z)
    (resident:∀a∈s.val,sites R (homes) bc.le a∈Z)
    {Y ι:Type}[Countable ι]{p':BudgetPoint}{o':V→Site (R.family.side i per)}
    (next:Lamps Y ι G p' o' (marks))(z:Y)
    (borel:Measurable (fun U=>(Poly.pass (bare next z U)).part s))
    {B e:ℝ}(bp:0≤B)(ep':0≤e)
    (gross:∀U,‖(Poly.pass (((lamps).join P.output.old).log x U)).part s-
      (Poly.pass (bare next z U)).part s‖ ≤ B)
    (healthy:∀U,(∀a∈s.val,Healthy (Ψ i).p.threshold (halo (Ψ i).p.B {(homes) a}) U) →
      ‖(Poly.pass (((lamps).join P.output.old).log x U)).part s-(Poly.pass (bare next z U)).part s‖ ≤ e):
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^q
    let src:=Stoop.radius P.w (max 1 (cash+debt))
    let fee:=Poly.toll (wallet R src bc.le) s
    let roof:=((shards (marks) s).card:ℝ)+4*(fee+WilsonOriginalFlatOccupiedRate.bill (Ψ b).p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b
    let exception:=s.val.card*(4*hitWidth (Ψ i).p*Real.exp ((Ψ i).p.supportExponent+2)*
      R.alloy.B.a.clock.hatBeta i*R.alloy.B.a.clock.forcedAllowance i)
    fee*‖reading R (N:=N) (fun U=>(LocalComparison.actualPush R.family N per i (physical x) U).part s)
      v (vb.trans bc.le)-reading R (N:=N) (fun U=>((Ψ i).eval U:ℂ)*(Poly.pass (bare next z U)).part s)
      v (vb.trans bc.le)‖ ≤ WilsonOriginalOccupiedWallet.inverseAmplitude n κ*WilsonOriginalOccupiedStencil.price n*roof+
      fee*(e+B*exception):=by
  intro debt src fee roof exception
  letI:Countable P.outputIndex:=P.outputCount
  letI:Countable P.modelIndex:=P.modelCount
  letI : Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  letI:Nonempty (Wallet actors):=⟨x⟩
  obtain ⟨smooth,_,old,hard,field⟩:=WilsonOriginalFiledSuccessorIncome.original
    R hk D Q π Γ Ψ books hi cut ahead actors pieces grades order shelf seats physical P simple way course
    pole q sourced hardFloor deep aged ep opened
  let A:=posted (lamps) P.output.old P.output.hard
  let factor₀:=max 1 (cash+debt)
  have one:1≤factor₀:=le_max_left ..
  have pos:0<factor₀:=zero_lt_one.trans_le one
  have hw:=P.issued.earning.positive
  have fresh:∀v,0<src v:=fun v=>div_pos (hw v) pos
  have whole:A.E.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) (cash+debt):=Lamps.joinPaid smooth old
  have smaller:=Stoop.tighten P.w A.E hw one whole
  have sale:factor₀⁻¹*(cash+debt)≤1:=(inv_mul_le_one₀ pos).2 (le_max_right ..)
  have reg:=weaker A.E src fresh (Lamps.loan_monotone _ smaller sale)
    (show (Ψ i).p.supportExponent ≤ (Ψ i).p.supportExponent+2 by linarith)
  have actual:=WilsonOriginalTwoFlatDated.original R way D Q π Γ Ψ course ticket (homes) A src fresh
    simple floor (uv.trans vb) fixed capture uv vb bc cut.le Z center home stage load_ok cap s resident n np
    (load_ok s) tiny reg (Stoop.leaves P.w A.K hw one hard) x cut
    (fun U=>(Poly.pass (bare next z U)).part s) borel bp ep' gross healthy
  simp_rw [field x]
  exact actual

end YM.Integration.WilsonOriginalTwoFlatSuccessor
end
