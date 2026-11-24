import YM.Integration.WilsonOriginalQBirthWallet
import YM.Integration.WilsonOriginalProjectedCurvatureEvaluation

/-! The measured deposition, original payout, and finite-forest filing on the prepaid source wallet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerMeasuredEarnings
open Function Filter Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open ComparisonDensity.Address MergeProof MergeProof.Replicums Comparison.Density.RenderM FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open ConnectedActivityE6 Push.PriceCompiler FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ) {ψ:ℕ→ℕ}
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root seat)
  (posted:Spill.Raffle.Warm G root R.alloy.delay ψ)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

variable (books:Mentor.Offices.Books root R.rolls seat ψ) (forecast:Mentor.Forecast root R.rolls seat ψ books)
  (education:Mentor.Educated root R.rolls seat R.kit.shape R.kit.scout ψ books R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))
  (calendar:MintClock.Regency root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (hospital:MintClock.Hospital root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (pass:Pass root seat R.alloy R.kit)

include income way ticket posted active calendar hospital education
/-- The original normalized curvature input, its actual physical course, and every returned signed test
use one allowance chosen at the measured date before either finite regulator. -/
theorem atBirth (K grade q target:ℕ) (ranked:rank ≤ grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε) {C:ℝ} {b:ℕ}
    (submit: WilsonOriginalQBirthWallet.At (WilsonOriginalProjectedCurvatureOnCard.original R hG J Q u μ extra w root income K grade q positive εpos) C b) :
    WilsonOriginalQBirthWallet.At (original R hG J Q u μ extra w root seat way ticket posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos) C b := by
  unfold WilsonOriginalQBirthWallet.At at submit ⊢
  let horizon:=Burn.horizon (grade+v+h)
  let minimum:=horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h)
  let firstRow:=WilsonOriginalProjectedCurvatureScheduledField.earliest R u
  have next:Filter.Tendsto (fun m:ℕ=>m+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [submit,R.alloy.B.a.fits.deep.eventually_ge_atTop v,
    (R.alloy.B.a.fits.deep.comp next).eventually_ge_atTop minimum,next.eventually_ge_atTop firstRow]
    with m booked width qualified high
  intro op epoch count level vac Ω
  have load:op.count ≤ Burn.horizon epoch.vac+2:=by rw [count,vac]; unfold Burn.horizon; omega
  have paid:=WilsonMovingMentorPagePrice.at_date R books forecast active calendar m op epoch grade v width
    (by omega) load
  have large:4 ≤ Ω:=paid.2.1
  have one:1 ≤ Ω:=by linarith
  have roof:Ω ≤ (β̂ (m+1))^(Beaming.grain (J₀ m)):=paid.2.2.1.trans (min_le_right _ _)
  refine ⟨large,roof,?_⟩
  intro N p o orders capped before π Γ H first start course card journey upper top D σ η X a weights g
  obtain ⟨vote₀,rows₀,restore⟩:=booked (vac ▸ card) Ω one roof N p o orders capped before
  have vote:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) grade op.count op.stage epoch.vac (J₀ m):=by
    rw [count,level,vac]
    exact vote₀
  have rows:Scene.Armada X weights (fun _=>t) σ Ω⁻¹ rank h v:=rows₀
  have seated:Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) Ω⁻¹ rank h v:=by
    rw [vac]; exact rows
  have installed:Scene.Armada X weights (fun _=>t) σ 1 rank h v:=
    { toMinistry:=rows.toMinistry,positive:=rows.positive,purchases:=rows.purchases,honor:=rows.honor
      suggests:=fun x=>Push.AbsoluteSums.budget_loosen (rows.suggests x) (inv_le_one_of_one_le₀ one) }
  have ready (s:Slot u):R.family.ref s.2.size ≤ m+1:=
    (Finset.le_sup (f:=fun s:Slot u=>R.family.ref s.2.size) (Finset.mem_univ s)).trans high
  change horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h) ≤ J₀ (m+1) at qualified
  have selected:horizon ≤ J₀ (m+1):=by omega
  obtain ⟨incoming,retained,read⟩:=WilsonOriginalProjectedCurvatureHardDate.measured (R:=R) (Q:=Q) (target:=target)
    (D:=D) (u:=u) (μ:=η) (orders:=orders) (extra:=extra) (hG:=hG) (ready:=ready) (root:=root)
    (seat:=seat) (way:=way) (ticket:=ticket) (posted:=posted) (story:=course) (start:=Nat.le_succ_of_le start)
    (reached:=before) (top:=top) installed selected (by omega) (by omega) (by omega) (by omega)
  obtain ⟨gross,sealed,medal,Z,stamped,_⟩:=WilsonCoherentMayerPublishedSlip.original
    (R:=R) (simple:=hG) (root:=root) (table:=seat) (ψ:=ψ) (books:=books) (pass:=pass)
    (education:=education) (op:=op) (epoch:=epoch) (card:=card) (journey:=journey) (upper:=upper)
    (course:=course) (start:=start) (before:=before) (M:=X) (w:=weights) (positive:=rows.positive)
    (voter:=vote) (input:=incoming) (y:=WilsonOriginalPointModes.unit (ActualRunQlocalNativeTuple.orbit D)) (forecast:=forecast) (hospital:=hospital)
    (vol:=v) (tolls:=fun _=>t) (q:=target) (height:=load) (room:=width) (j:=rank) (k:=h) («v»:=v) (rows:=seated) (jet:=ranked) (crew:=count.ge) (placed:=le_refl v) (retained:=retained)
  refine ⟨restore,rows.positive,vote,seated,gross,incoming,retained,read,sealed,medal,Z,stamped,fun y=>?_⟩
  exact WilsonOriginalProjectedCurvatureCourseNotice.original (R:=R) (simple:=hG) (root:=root) (table:=seat)
    (ψ:=ψ) (books:=books) (pass:=pass) (education:=education) (op:=op) (epoch:=epoch) (card:=card)
    (journey:=journey) (course:=course) (start:=start) (before:=before) (M:=X)
    (w:=weights) (positive:=rows.positive) (voter:=vote) (input:=incoming) (sealed:=sealed) (y:=y) Z

end YM.Integration.WilsonCoherentMayerMeasuredEarnings

namespace YM.Integration.WilsonOriginalProjectedCurvaturePassage
open Function Filter Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open ComparisonDensity.Address MergeProof MergeProof.Replicums Comparison.Density.RenderM FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open ConnectedActivityE6 Push.PriceCompiler FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ) {ψ:ℕ→ℕ}
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root seat)
  (posted:Spill.Raffle.Warm G root R.alloy.delay ψ)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

variable (books:Mentor.Offices.Books root R.rolls seat ψ) (forecast:Mentor.Forecast root R.rolls seat ψ books)
  (education:Mentor.Educated root R.rolls seat R.kit.shape R.kit.scout ψ books R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))
  (calendar:MintClock.Regency root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (hospital:MintClock.Hospital root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (pass:Pass root seat R.alloy R.kit)

open QuadraticLocal.Advent WilsonOriginalProjectedCurvatureTableau
include income way ticket posted active calendar hospital education pass
/-- One allowance before both regulators buys the full deposited curvature source and its
countably signed successor on the same physical course. -/
theorem atBirth (K grade q target:ℕ) (ranked:rank ≤ grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε) {C:ℝ} {b:ℕ}
    (funded: WilsonOriginalQBirthWallet.At (WilsonCoherentMayerMeasuredEarnings.original R hG J Q u μ extra w root seat way ticket posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos) C b) :
    WilsonOriginalQBirthWallet.At (original R hG J Q u μ extra w root seat way ticket posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos) C b := by
  unfold WilsonOriginalQBirthWallet.At at funded ⊢
  let horizon:=Burn.horizon (grade+v+h)
  let minimum:=horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h)
  let firstRow:=WilsonOriginalProjectedCurvatureScheduledField.earliest R u
  have next:Filter.Tendsto (fun m:ℕ=>m+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [funded,R.alloy.B.a.fits.deep.eventually_ge_atTop v,
    (R.alloy.B.a.fits.deep.comp next).eventually_ge_atTop minimum,next.eventually_ge_atTop firstRow]
    with m purchased width qualified high
  intro op epoch count level vac Ω
  obtain ⟨large,roof,booked⟩:=purchased op epoch count level vac
  refine ⟨large,roof,?_⟩
  intro N p o orders capped before π Γ H first start course hk lesson top D σ η X a weights g
  obtain ⟨restore,signed,voter,seated,_⟩:=booked N p o orders capped before π Γ H first start
    course lesson.entry lesson.studied lesson.ticket top
  have one:1≤Ω:=by linarith
  have rows:Scene.Armada X weights (fun _=>t) σ Ω⁻¹ rank h v:=by simpa only [vac] using seated
  have installed:Scene.Armada X weights (fun _=>t) σ 1 rank h v:=
    { toMinistry:=rows.toMinistry,positive:=rows.positive,purchases:=rows.purchases,honor:=rows.honor
      suggests:=fun x=>Push.AbsoluteSums.budget_loosen (rows.suggests x) (inv_le_one_of_one_le₀ one) }
  have ready (s:Slot u):R.family.ref s.2.size ≤ m+1:=
    (Finset.le_sup (f:=fun s:Slot u=>R.family.ref s.2.size) (Finset.mem_univ s)).trans high
  change horizon+rank+v+h+(target+Spill.Raffle.pad (rank+v+1)*h) ≤ J₀ (m+1) at qualified
  have selected:horizon ≤ J₀ (m+1):=by omega
  obtain ⟨incoming,taut,crown,old,hard,read⟩:=WilsonOriginalProjectedCurvatureAttunedDate.measured
    (R:=R) (Q:=Q) (target:=target) (D:=D) (u:=u) (μ:=η) (orders:=orders) (extra:=extra)
    (hG:=hG) (ready:=ready) (root:=root) (seat:=seat) (way:=way) (ticket:=ticket) (posted:=posted)
    (story:=course) (start:=Nat.le_succ_of_le start) (reached:=before) (top:=top) installed selected
    (by omega) (by omega) (by omega) (by omega)
  have step:Scene.Armada X weights (fun _=>t) (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac)
      (J₀ (m+1))) Ω⁻¹ grade op.count v:=
    ⟨⟨fun s=>(seated.quota s).trans count.ge,fun s=>seated.crew s⟩,seated.positive,
     seated.suggests,⟨seated.purchases.spend,fun s=>
      ⟨((seated.purchases.usable s).1).trans ranked,(seated.purchases.usable s).2⟩⟩,seated.honor⟩
  refine ⟨restore,signed,voter,incoming,read,step,?_⟩
  obtain ⟨cal⟩:=Oak.agrees R hk root seat π Γ H course start before lesson
  have load:op.count≤Burn.horizon epoch.vac+2:=by rw [count,vac]; unfold Burn.horizon; omega
  have held:=Graces.glyphBound R.family.path.levels (m+1)
  have at_least:1≤β̂ (m+1):=(R.alloy.B.a.fits.delayed (m+1)).le
  have raised:(β̂ (m+1))^(-(target:ℝ))≤1:=Real.rpow_le_one_of_one_le_of_nonpos at_least
    (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hardOne:=incoming.hard.mono hard ((mul_le_mul_of_nonneg_right raised held.1.le).trans
    ((one_mul _).trans_le held.2))
  have pos:0<(β̂ (m+1))^(-(grade:ℝ)):=Real.rpow_pos_of_pos (zero_lt_one.trans_le at_least) _
  have small:(β̂ (m+1))^(-(grade:ℝ))≤1:=Real.rpow_le_one_of_one_le_of_nonpos at_least
    (neg_nonpos.mpr (Nat.cast_nonneg _))
  have oldPaid:=incoming.old.loan_monotone (old (H (m+1)).p.supportExponent (H (m+1)).p.B) pos.le
  exact Oak.Buffered.physical (R:=R) (g:=hG) (hk:=hk) (D:=root) (Q:=seat) (π:=π) (Γ:=Γ)
    (Ψ:=H) («v»:=course) (Q0:=books) (paidCourse:=pass) (courses:=education) (hℓ:=start)
    (hz:=before) (Pt:=op) (V₁:=lesson) (V₂:=cal) (Qa:=forecast) (hQ:=hospital)
    (Actors:=actors D) (U:=fun i=>(nulls D i).restrictScalars ℝ) (M:=X) (Z₁:=incoming)
    (w:=weights) (ηL:=fun _=>t) (jJ:=grade) (Vh:=v) (Vₜ:=voter) (e_E:=(β̂ (m+1))^(-(grade:ℝ)))
    (c_P:=Ω⁻¹) (hJ:=load) (hv:=width) (Yv:=step)
    (hM:=WilsonOriginalProjectedCurvatureTableau.real D Q u η orders N σ extra)
    (y:=WilsonOriginalPointModes.unit (ActualRunQlocalNativeTuple.orbit D)) (hL:=taut)
    (hY:=crown) (hO:=oldPaid) (hP₁:=hardOne) (he_C:=inv_le_one_of_one_le₀ one) (h0:=pos) (ht₁:=small)

end YM.Integration.WilsonOriginalProjectedCurvaturePassage

namespace YM.Integration.WilsonOriginalProjectedCurvatureEvaluation
open Function Filter Finset Lattice Wilson RG Source Labels Marker Ac
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato LocalComparison
open ComparisonDensity.Address MergeProof MergeProof.Replicums Comparison.Density.RenderM FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureSalary
open QuadraticLocal QuadraticLocal.Earn Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open ConnectedActivityE6 Push.PriceCompiler FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ) {ψ:ℕ→ℕ}
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root seat)
  (posted:Spill.Raffle.Warm G root R.alloy.delay ψ)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

variable (books:Mentor.Offices.Books root R.rolls seat ψ) (forecast:Mentor.Forecast root R.rolls seat ψ books)
  (education:Mentor.Educated root R.rolls seat R.kit.shape R.kit.scout ψ books R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))
  (calendar:MintClock.Regency root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (hospital:MintClock.Hospital root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (pass:Pass root seat R.alloy R.kit)

open QuadraticLocal.Advent WilsonOriginalProjectedCurvatureTableau Laurent Stationary
open Tree
include income way ticket posted active calendar hospital education pass
/-- On the chosen physical course and all its regulators, compare the actual pushed original source
with the complete normalized finite filing on its genuine returned lower roster. -/
theorem atBirth (K grade q target:ℕ) (ranked:rank ≤ grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε) {C:ℝ} {b:ℕ}
    (funded: WilsonOriginalQBirthWallet.At (WilsonOriginalProjectedCurvaturePassage.original R hG J Q u μ extra w root seat way ticket posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos) C b) :
    WilsonOriginalQBirthWallet.At (original R hG J Q u μ extra w root seat way ticket posted income books forecast education active calendar hospital pass K grade q target ranked positive εpos) C b := by
  unfold WilsonOriginalQBirthWallet.At at funded ⊢
  have next:Filter.Tendsto (fun m:ℕ=>m+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [funded,next.eventually_ge_atTop (WilsonCoherentMayerRosterWindingRun.firstDate R hG)]
    with m purchased openDate
  intro op epoch count stage cap Ω
  obtain ⟨large,roof,selected⟩:=purchased op epoch count stage cap
  refine ⟨large,roof,?_⟩
  intro N p o orders capped before π Γ H first start course hk lesson top D σ η X a weights g
  obtain ⟨restored,positive,voter,incoming,field,upper,ξ,counted,out,story⟩:=
    selected N p o orders capped before π Γ H first start course hk lesson top
  refine ⟨restored,positive,voter,incoming,field,upper,ξ,counted,out,story,?_,?_⟩
  · intro y
    have source:(Tint.Patrol.picture X incoming).density y=
        ((ActualOriginalQInput.input Q D u η orders hG N before).leaf
          (testInclusion (ActualRunQlocalNativeTuple.orbit D) y)).density:=funext (field y)
    have pushed:LocalComparison.actualPush R.family N p m ((Tint.Patrol.picture X incoming).density y)=
        (Tint.Patrol.report (Oak.student (n:=p) R hk root seat π Γ books start op lesson forecast
          (actors D) X grade voter) out (Coat.gStep (H (m+1)).beta)).density y:=story.reads y
    rw [(course.1.walk (m+1) (Nat.le_succ_of_le start) before).beta] at pushed
    exact (congrArg (LocalComparison.actualPush R.family N p m) source.symm).trans pushed
  · intro x F tag A
    have small:Ω⁻¹≤1:=inv_le_one_of_one_le₀ (by linarith)
    exact (WilsonOriginalMarkedEvaluation.assessed R hk root seat π Γ H course books start before op
      lesson forecast (actors D) X weights (fun _=>t) grade v voter Ω⁻¹ upper x F tag A
      (fun i=>(nulls D i).restrictScalars ℝ) incoming ((β̂ (m+1))^(-(grade:ℝ))) out story small hG openDate).2

end YM.Integration.WilsonOriginalProjectedCurvatureEvaluation

end
