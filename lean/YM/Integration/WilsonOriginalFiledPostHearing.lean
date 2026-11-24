import YM.Integration.WilsonOriginalBetweenFiledPrints

/-! The earlier normalized measurement of the genuine Wilson successor and an
independently affixed lower compact print on the same group configurations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledPostHearing
open Filter MeasureTheory Multi
open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors AnalyticBridge.SectorAffine.Offset
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
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

include cut in
set_option maxHeartbeats 600000 in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ i)(fixed:WilsonSingleHardRadius.first R simple ≤ u)
    {d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)(capture:WilsonCenteredCaptureClock.first R simple ≤ i)
    (pole q p d₀:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged ep ≤ i)
    {tol:ℝ}(pos:0<tol)(hardLate:WilsonSingleHardRadius.start R simple p pos ≤ i)
    (divLate:(eventually_atTop.mp (WilsonCenteredDividedRoom.original R simple)).choose ≤ i)
    (x:Wallet actors)(s:(marks).Mode)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (p+d₀*s.val.card) pos)).choose ≤ i)
    (Z:Support (R.family.side i per))(y:Site (R.family.side i per))(center:y∈Z)
    (resident:∀a∈s.val,homes a∈Z)(rad:ℕ)(near:∀a∈s.val,separation (homes a) y ≤ rad)
    {Y ι:Type}[Countable ι]{p':BudgetPoint}{o':V→Site (R.family.side i per)}
    (next:Lamps Y ι G p' o' (marks))(z:Y)(w':V→ℝ)(hw':∀v,0<w' v){α' C':ℝ}(win:0 ≤ α')
    (sold:Gross next w' p'.B α' C')
    {W W':ℝ}(wp:0 ≤ W)(inlet:∀t:Hot (marks),t.val.val⊆s.val→(Poly.toll P.w t.val)⁻¹ ≤ W)
    (outlet:∀t:Hot (marks),t.val.val⊆s.val→(Poly.toll w' t.val)⁻¹ ≤ W')
    {α M δ:ℝ}(strength:(Ψ i).p.supportExponent ≤ α)(tube:LinkTube G)(front:Hot (marks)→V)
    (member:∀t,front t∈t.val.val)(mp:0 ≤ M)(dp:0 ≤ δ)
    (sources:W*(((2:ℝ)^(order+shelf+1)/oldG^pole)*cash) ≤ M*β^d₀ ∧ W'*C' ≤ M*β^d₀)
    (rows:∀(t:Hot (marks)),t.val.val⊆s.val→Row (Ψ i).p tube (homes (front t))
      (fun U=>(bare (lamps) x U).part t.val) (fun U=>(bare next z U).part t.val))
    (due:∀t ht,(rows t ht).price ≤ δ){j:ℕ}(uj:u ≤ j)(ji:j+1 ≤ i):
    let raw:=((2:ℝ)^(order+shelf+1)/oldG^pole)*cash
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^q
    let oldFee:=change s (W*cash) (W*debt)
    let fee:=WilsonOriginalFlatOccupiedRate.bill (Ψ i).p Z (cash+debt) s.val.card+
      roof (Ψ i).p Z cash s.val.card+roof (Ψ i).p Z raw s.val.card
    ‖reading R (N:=N) (fun U=>(LocalComparison.actualPush R.family N per i (physical x) U).part s-
        ((Ψ i).eval U:ℂ)*(Poly.pass (bare next z U)).part s) j ((Nat.le_succ j).trans ji)‖ ≤ 
      oldFee+change s (M*β^d₀) δ+(oldFee+2*cost s M)*s.val.card*(4*Real.exp (α+2))*tol/β^p+
        4*(1+(Poly.toll P.w s)⁻¹*fee)*tol/β^p:=by
  intro raw debt oldFee fee
  letI:Countable P.outputIndex:=P.outputCount
  letI:Countable P.modelIndex:=P.modelCount
  letI : Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  obtain ⟨regular,gross,old,hard,field⟩:=WilsonOriginalFiledSuccessorIncome.original
    R hk D Q π Γ Ψ books hi cut ahead actors pieces grades order shelf seats physical P simple way course
    pole q sourced hardFloor deep aged ep opened
  have width0:0 ≤ (Ψ i).p.supportExponent+2:=by linarith only [(Ψ i).p.exponent_pos]
  have hw:=P.issued.earning.positive
  have cp:0 ≤ cash:=by obtain ⟨_,_,_,addr⟩:=regular.budget;exact budget_nonneg (addr y)
  have rp:0 ≤ raw:=by obtain ⟨_,_,_,addr⟩:=gross;exact budget_nonneg (addr y)
  have np:0 ≤ C':=by obtain ⟨_,_,_,addr⟩:=sold;exact budget_nonneg (addr y)
  have hp:0 ≤ debt:=by obtain ⟨_,_,_,addr⟩:=old.budget;exact budget_nonneg (addr y)
  obtain ⟨quiet,borel,salary⟩:=WilsonOriginalBetweenFiledPrints.original (lamps) P.output.old P.output.hard next
    P.w w' hw hw' width0 win regular gross old sold x z s rp np inlet outlet sources
  simp_rw [field x]
  exact WilsonOriginalFlatFiledHearing.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p d₀ pos hardLate divLate homes (lamps) P.output.old P.output.hard x s late Z y center resident rad
    near P.w hw cp rp hp wp inlet regular gross old hard strength tube front member (bare next z) quiet borel
    mp dp salary rows due uj ji

end YM.Integration.WilsonOriginalFiledPostHearing
