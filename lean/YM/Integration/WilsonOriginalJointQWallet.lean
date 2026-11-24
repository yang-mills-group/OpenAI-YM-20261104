import YM.Integration.WilsonOriginalSignedDatedFinite
import YM.Integration.WilsonOriginalFreshQAtReceivedDate
import YM.Integration.WilsonOriginalSignedQAdmission
import YM.Integration.WilsonOriginalMixedFiniteVoter
import YM.Integration.WilsonOriginalMixedStampedFinite
import YM.Integration.WilsonOriginalMeasuredStampCoefficients

/-! On two adjacent dates of the actual course, retain the complete measured old rescaling and the independent fresh source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalJointQWallet
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open Multi Exterior WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open private staff from YM.Integration.WilsonOriginalClubSourcePackets
open Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonMixedPassportVote
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple) {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (request : Request V) (freshQ : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B) (μ : ℝ) (extra : V → ℕ) (free : V → ℝ)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (K q : ℕ) (freePos : ∀ v, 0 < free v) {ε : ℝ} (allow : 0 < ε)
local notation "offer" => WilsonOriginalMixedFiniteVoter.original R request freshQ u μ extra free D income simple K q freePos allow
local notation "factor" => Classical.choose offer
local notation "exponent" => (Classical.choose_spec offer).2.choose

variable {m j N per k : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (Q : D.Tab R.rolls) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
  (Ψ : ∀ l, RG.Rep G (R.family.side l per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
  (books : Mentor.Offices.Books D R.rolls Q φ) (floor : m ≤ j) (cut : j+1 < N)
local notation "depth" => Burn.horizon k+2
local notation "T₀" => AllOrder.Floe.Step.tape depth
variable (op : Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson : Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))) (ahead : Mentor.Forecast D R.rolls Q φ books)
  {ι : Type} {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  {P : Earn.Passport (R.family.side ((j+1)+1) per) V}
  (actors : ∀ v, Set (X v)) (M : ι → Row P (Stock.census V) G (Affinity.Wallet actors))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J ((j+1)+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J (j+1)))
local notation "M₁" => Oak.student (m:=m) (i:=j+1) (n:=per) (N:=N) (k:=k) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead actors M order voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) lesson
local notation "oldRows" => Mutation.stamp M₁ (Γ (j+1)) ζ depth order
local notation "file" => litP D R.alloy Q (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))) lesson.entry
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead order shelf
local notation "rebate" => Oak.rebate R hk D Q π Γ (floor.trans (Nat.le_succ j)) op lesson
local notation "page" => WilsonMovingMentorPageRefund.cap R j
local notation "tQ" => (fun _ : V => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u)
variable (sites : V → Site (R.family.side (j+1) per)) (orders : V → ℕ)
local notation "datum" => ActualOriginalQPointSetup.pointDatum R request per (j+1) sites
local notation "η" => (μ+R.family.S.scale N-R.family.S.scale (j+1))-R.family.S.scale N
local notation "newRows" => WilsonOriginalProjectedCurvatureLamps.cohort freshQ datum u η orders N σ extra

variable (pieces₀:∀ v,Submodule ℝ (X v)) (old fresh:Finset V) (sep:Disjoint old fresh) (zeroA:∀v,0∈actors v)
  (warm:QuadraticLocal.Spill.Raffle.Warm G D R.alloy.delay φ)
local notation "freshA" => WilsonOriginalProjectedCurvatureTableau.actors datum
local notation "Knew" => (fun v=>(WilsonOriginalProjectedCurvatureTableau.nulls datum v).restrictScalars ℝ)
local notation "A₂" => WilsonMixedTestTableau.actors actors freshA
local notation "l" => WilsonMixedTestTableau.left actors freshA old zeroA
local notation "rTest" => WilsonMixedTestTableau.right actors freshA fresh (WilsonOriginalMixedTestTableau.zero datum)
local notation "mixed" => WilsonMixedFaceLog.routed oldRows newRows old fresh sep l rTest
local notation "mixGrades" => choice old grades tQ
local notation "sheet" => Pane.panel R.alloy (j+1) (R.alloy.B.a.S.oneStep (j+1) per).exact_size
local notation "home" => P.coarser (sheet).ratio
local notation "xβ" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "paidScale" => factor*xβ^(exponent+1)
local notation "hQ" => ActualOriginalQLayout.rankCap R u+Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u+1
local notation "risk" => (xβ^QuadraticLocal.Spill.Raffle.pad hQ)
local notation "incomeQ" => WilsonOriginalFreshQAtReceivedDate.prepaid R simple request freshQ u μ extra free D income warm K freePos
local notation "entrance" => (Classical.choose_spec incomeQ).2.choose_spec
def firstBirth : ℕ := (eventually_atTop.mp entrance).choose
local notation "m₀" => firstBirth R simple request freshQ u μ extra free D income K freePos warm
local notation "hβ" => R.alloy.B.a.clock.J (j+1)

private theorem lower {ω V α:Type} {s:Side} [DecidableEq V] [Fintype V]
    {P:Earn.Passport s V} {marks:Census V} {θ c:ℝ} {a b t:ℕ} {w u:V → ℝ} {fees:V → ℕ}
    (M:ω → QuadraticLocal.Earn.Row P marks G α) (granted:QuadraticLocal.Earn.Scene.Armada M w fees θ c a b t)
    (positive:∀v,0<u v) (fits:∀v,u v ≤ w v) :
    QuadraticLocal.Earn.Scene.Armada M u fees θ c a b t:=by
  refine ⟨granted.toMinistry,positive,?_,granted.purchases,granted.honor⟩
  intro x
  apply Push.AbsoluteSums.budget_mono (granted.suggests x)
  · intro i
    split
    · exact mul_nonneg (Marker.Poly.worth positive _).le (mul_nonneg (M i).sound.le (Real.exp_pos _).le)
    · exact le_rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun v _=>(positive v).le) (fun v _=>fits v))
        (mul_nonneg (M i).sound.le (Real.exp_pos _).le)
    · exact le_rfl

include course path cut in
theorem original (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (cost:ℝ) (load:op.count ≤ depth) (narrow:shelf ≤ R.alloy.B.a.clock.J (j+1)) (fits:order ≤ Burn.horizon k+1)
    (packed:order+shelf ≤ depth) (late:WilsonOriginalMixedStampedFinite.firstDate R simple request freshQ u μ extra free D income K q freePos allow ≤ j)
    (funded:m₀ ≤ j+1) (Ω:ℝ) (one:1 ≤ Ω) (cap:Ω ≤ page) (ordersOK:∀v,orders v ≤ K)
    (rank:ActualOriginalQLayout.rankCap R u ≤ order) (count:Fintype.card V ≤ op.count)
    (level:gradeTotal old grades tQ ≤ shelf) (oldPos:∀v,0<w v)
    (x:Affinity.Wallet A₂) (F:Forest (R.family.path.levels.clock.op j per).ratio)
    (tag:(R.family.path.levels.clock.op j per).Choices) (b₀:fieldDir G (R.family.side j per) 1) (row:ℕ) :
    ∃ (wQ joined:V → ℝ) (rent gross fare:ℝ),
      (∀v,0<wQ v) ∧ (∀v,0<joined v) ∧ (∀v ∈ old,joined v ≤ w v) ∧
      gross ≤ Willow.haloSlack (Ψ (j+1)).p.B ∧
      WilsonOriginalFreshQWallet.Return freshQ datum u η orders N σ extra actors pieces₀ home old fresh sep
        (Ψ (j+1)).p wQ joined rent gross ∧
      (Scene.Armada M₁ w grades σ cost order op.count shelf →
        Scene.Armada mixed joined mixGrades σ fare order op.count shelf) ∧ fare ≤ Ω⁻¹ ∧
      (∀ v ∈ old,joined v=w v/(max 1 (Ω*(Oak.rebate R hk D Q π Γ (floor.trans (Nat.le_succ j)) op lesson*cost)))/2) ∧
      (∀ v ∈ fresh,joined v=min (free v/(paidScale*Ω)/2) (wQ v)) ∧
      ∀ v,wQ v=free v/((Classical.choose incomeQ*xβ^((Classical.choose_spec incomeQ).2.choose+1))*risk) := by
  let ΩQ:ℝ:=risk
  have βpos:0<xβ:=zero_lt_one.trans_le (R.alloy.B.a.fits.delayed (j+1)).le
  have posQ:0<ΩQ:=pow_pos βpos _
  have pageC:0<factor:=zero_lt_one.trans_le (Classical.choose_spec offer).1
  have saleC:0<Classical.choose incomeQ:=zero_lt_one.trans_le (Classical.choose_spec incomeQ).1
  let a:=paidScale
  let received:=Classical.choose incomeQ*xβ^((Classical.choose_spec incomeQ).2.choose+1)
  let wQ:=fun v=>free v/(received*ΩQ)
  let wOld:=fun v=>free v/(a*Ω)
  let cc:=Oak.rebate R hk D Q π Γ (floor.trans (Nat.le_succ j)) op lesson*cost
  let shrink:=max 1 (Ω*cc)
  let offered:=QuadraticLocal.Stoop.radius (choice old (QuadraticLocal.Stoop.radius w shrink) wOld) 2
  let joined:=fun v=>if v ∈ old then offered v else min (offered v) (wQ v)
  let charge:=(2:ℝ)⁻¹*(shrink⁻¹*cc+Ω⁻¹)
  have pQ:∀v,0<wQ v:=fun v=>div_pos (freePos v) (mul_pos (mul_pos saleC (pow_pos βpos _)) posQ)
  have oldPositive:∀v,0<wOld v:=fun v=>div_pos (freePos v) (mul_pos (mul_pos pageC (pow_pos βpos _)) (zero_lt_one.trans_le one))
  have shorter:1 ≤ shrink:=le_max_left _ _
  have both:∀v,0<offered v:=by
    intro v
    apply div_pos _ (by norm_num)
    by_cases hv:v ∈ old
    · simpa only [choice,if_pos hv,QuadraticLocal.Stoop.radius] using div_pos (oldPos v) (zero_lt_one.trans_le shorter)
    · simpa only [choice,if_neg hv] using oldPositive v
  have pos:∀v,0<joined v:=by
    intro v
    by_cases hv:v ∈ old
    · simpa only [joined,if_pos hv] using both v
    · simpa only [joined,if_neg hv] using lt_min (both v) (pQ v)
  have small:∀v,joined v ≤ offered v:=by
    intro v
    by_cases hv:v ∈ old
    · simp only [joined,if_pos hv,le_refl]
    · simp only [joined,if_neg hv,min_le_left]
  have started:∀v ∈ old,joined v ≤ w v:=by
    intro v hv
    simp only [joined,if_pos hv,offered,QuadraticLocal.Stoop.radius,choice]
    exact (div_le_self (div_nonneg (oldPos v).le (zero_le_one.trans shorter)) (by norm_num)).trans (div_le_self (oldPos v).le shorter)
  have bought:∀v ∈ fresh,joined v ≤ wQ v:=by
    intro v hv
    have no:v ∉ old:=fun h=>Finset.disjoint_left.mp sep h hv
    simp only [joined,if_neg no,min_le_right]
  have source:=(eventually_atTop.mp entrance).choose_spec (j+1) funded (Burn.horizon k)
    ((Nat.le_add_right (Burn.horizon k) 2).trans (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
    ΩQ posQ N per sites orders ordersOK m k π Γ Ψ course (floor.trans (Nat.le_succ j)) cut.le X actors pieces₀ home old fresh sep joined pos bought
  have ceiling:=source.2.2
  have grossCap:_ ≤ Willow.haloSlack (Ψ (j+1)).p.B:=ceiling.trans (le_of_eq (by
    change ΩQ*Willow.haloSlack (Ψ (j+1)).p.B*ΩQ⁻¹=_
    field_simp [posQ.ne']))
  have oldCap:shrink⁻¹*cc ≤ Ω⁻¹:=by
    rw [←div_eq_inv_mul,inv_eq_one_div]
    apply (div_le_div_iff₀ (zero_lt_one.trans_le shorter) (zero_lt_one.trans_le one)).mpr
    simpa only [one_mul,mul_comm cc Ω] using (le_max_right 1 (Ω*cc))
  have feeCap:charge ≤ Ω⁻¹ := by dsimp only [charge]; linarith
  refine ⟨wQ,joined,_,_,charge,pQ,pos,started,grossCap,source.1,?_,feeCap,?_,?_,fun _=>rfl⟩
  case refine_2 =>
    intro v h
    simp only [joined,if_pos h,offered,QuadraticLocal.Stoop.radius,choice]
    rfl
  case refine_3 =>
    intro v h
    have outside:v ∉ old:=fun h₀=>Finset.disjoint_left.mp sep h₀ h
    simp only [joined,if_neg outside,offered,QuadraticLocal.Stoop.radius,choice]
    rfl
  intro issued
  have deposited:=WilsonOriginalSignedDatedFinite.measured R simple request freshQ u μ extra free D income K q freePos allow
    hk Q π Γ Ψ course path books floor cut op lesson ahead actors M w grades order shelf voter sites orders old fresh sep
    l rTest x pass month cost issued load narrow fits packed late Ω one cap ordersOK rank count level F tag b₀ row
  exact lower _ deposited.1 pos small
end YM.Integration.WilsonOriginalJointQWallet
