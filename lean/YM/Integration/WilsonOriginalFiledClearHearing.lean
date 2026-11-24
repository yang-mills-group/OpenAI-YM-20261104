import YM.Integration.WilsonOriginalFiledPostHearing
import YM.Integration.WilsonFirstReceivedGalleryRegular

/-! The last chronological Wilson edge at an actual clear retained field. Each proper
component keeps its own front and its old regular debt. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledClearHearing
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
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
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

private theorem clearRead {G:Gauge}{n:Side}{V X ι:Type}[DecidableEq V][Fintype V]
    {o:V→Site n}{P:Rep G n}{J:Census V}(A:Gallery X ι o P J)(x:X)(U:Config G n)
    (empty:flags P.p.threshold U=∅):
    ((P.eval U:ℂ)⁻¹) • A.density x U=Poly.pass (A.E.log x U):=by
  have vacuum:(P.eval U:ℂ)=(Real.exp (P.exponent U):ℂ):=by
    simp [Rep.eval,P.activities.gas_one P.p empty]
  rw [Gallery.density,WilsonFirstReceivedGalleryRegular.clear A x U empty,mul_one,vacuum,
    smul_smul,inv_mul_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (P.exponent U))),one_smul]

include cut in
set_option maxHeartbeats 600000 in
theorem original (simple:G.Simple)(way:WayStation R.kit)(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (pole q:ℕ)(sourced:∀t:(marks).Mode,(∑v∈t.val,grades v)+1 ≤ pole)
    (hardFloor:6*seats ≤ R.alloy.B.a.clock.J i)(deep:2*(q+1)+8 ≤ order)(aged:q+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0<ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged ep ≤ i)
    (x:Wallet actors)(s:(marks).Mode)
    {Y ι:Type}[Countable ι]{p':BudgetPoint}{o':V→Site (R.family.side i per)}
    (next:Lamps Y ι G p' o' (marks))(z:Y)(w':V→ℝ)(hw':∀v,0<w' v){α' C':ℝ}(win:0 ≤ α')
    (sold:Gross next w' p'.B α' C')
    {W W':ℝ}(wp:0 ≤ W)(w'p:0 ≤ W')(inlet:∀t:Hot (marks),t.val.val⊆s.val→(Poly.toll P.w t.val)⁻¹ ≤ W)
    (outlet:∀t:Hot (marks),t.val.val⊆s.val→(Poly.toll w' t.val)⁻¹ ≤ W')
    (tube:LinkTube G)(front:Hot (marks)→V){δ:ℝ}(dp:0 ≤ δ)
    (rows:∀(t:Hot (marks)),t.val.val⊆s.val→Row (Ψ i).p tube (homes (front t))
      (fun U=>(bare (lamps) x U).part t.val) (fun U=>(bare next z U).part t.val))
    (due:∀t ht,(rows t ht).price ≤ δ)(U:Config G (R.family.side i per))(clear:flags (Ψ i).p.threshold U=∅):
    let debt:=(8*Ω^P.op.count)*P.rent+ε*g^q
    ‖(((Ψ i).eval U:ℂ)⁻¹ • (LocalComparison.actualPush R.family N per i (physical x) U)).part s-
        (Poly.pass (bare next z U)).part s‖ ≤ change s (W'*C') (W*debt+δ):=by
  intro debt
  letI:Countable P.outputIndex:=P.outputCount
  letI:Countable P.modelIndex:=P.modelCount
  letI : Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books P.op
    (Oak.era R hk D Q π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  let A:=posted (lamps) P.output.old P.output.hard
  obtain ⟨reg,_,old,_,coincides⟩:=WilsonOriginalFiledSuccessorIncome.original
    R hk D Q π Γ Ψ books hi cut ahead actors pieces grades order shelf seats physical P simple way course
    pole q sourced hardFloor deep aged ep opened
  have width0:0 ≤ (Ψ i).p.supportExponent+2:=by linarith only [(Ψ i).p.exponent_pos]
  have hw:=P.issued.earning.positive
  have hp:0 ≤ debt:=by obtain ⟨_,_,_,addr⟩:=old.budget;exact budget_nonneg (addr 0)
  have cp:0 ≤ C':=by obtain ⟨_,_,_,addr⟩:=sold;exact budget_nonneg (addr 0)
  have good (X:Support (R.family.side i per)):Healthy (Ψ i).p.threshold X U:=by simp [Healthy,clear]
  have read:((Ψ i).eval U:ℂ)⁻¹ • (LocalComparison.actualPush R.family N per i (physical x) U)=
      Poly.pass (A.E.log x U):=by
    rw [coincides x]
    exact clearRead A x U clear
  have same:(lamps).log x U=bare (lamps) x U:=by
    unfold Lamps.log WilsonRootedKioskOccupiedSlip.bare
    apply tsum_congr
    intro a
    have h:=WilsonRootedKioskOccupiedSlip.healthy (lamps) x a U (good _)
    exact congrArg (Poly.send ((lamps).mode a)) (sub_eq_zero.mp h)
  rw [read]
  apply ordinary s (A.E.log x U) (bare next z U)
    ⟨A.E.quiet_of_hasSum x U ((Lamps.joinPaid reg old).sums width0 hw x U),
      WilsonRootedKioskCompleteFiling.quiet next hw' win sold z U⟩
    (mul_nonneg w'p cp) (add_nonneg (mul_nonneg wp hp) dp)
  intro t ht
  obtain ⟨v,hv⟩:=t.property
  have land:=WilsonCenteredRegularHit.component P.output.old P.w hw width0 old x U t.val v hv
  have head:=WilsonOriginalFlatHull.healthy (rows t ht).crop U (good _)
  have bound:‖(bare next z U).part t.val‖ ≤ (Poly.toll w' t.val)⁻¹*C':=by
    rw [←mul_le_mul_iff_right₀ (Poly.worth hw' t.val),←mul_assoc,
      mul_inv_cancel₀ (Poly.worth hw' t.val).ne',one_mul]
    exact WilsonReceivedWholeFieldMask.whole next hw' win sold z U t.val v hv
  refine ⟨bound.trans (mul_le_mul_of_nonneg_right (outlet t ht) cp),?_⟩
  have joined: A.E.log x U=bare (lamps) x U+P.output.old.log x U:=
    (Lamps.joinLog x U (reg.sums width0 hw x U) (old.sums width0 hw x U)).trans (congrArg (·+_) same)
  rw [joined]
  change ‖(bare (lamps) x U).part t.val+(P.output.old.log x U).part t.val-(bare next z U).part t.val‖ ≤ _
  rw [show (bare (lamps) x U).part t.val+(P.output.old.log x U).part t.val-(bare next z U).part t.val=
      (P.output.old.log x U).part t.val+((bare (lamps) x U).part t.val-(bare next z U).part t.val) by abel]
  exact (norm_add_le ..).trans (add_le_add (land.trans (mul_le_mul_of_nonneg_right (inlet t ht) hp))
    (head.trans (due t ht)))

end YM.Integration.WilsonOriginalFiledClearHearing
