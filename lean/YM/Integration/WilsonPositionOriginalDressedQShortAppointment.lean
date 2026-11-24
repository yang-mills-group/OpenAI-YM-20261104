import YM.Integration.WilsonPositionOriginalDressedQResidualSquare
import YM.Integration.WilsonPositionOriginalDressedQCutClock
import YM.Integration.WilsonPositionOriginalDressedQEnrolledSale
import YM.Integration.WilsonPositionOriginalDressedQPointArms
import YM.Integration.WilsonPositionOriginalDressedQWithdrawal
import YM.Integration.WilsonPositionOriginalDressedQMeasuredPane

/-! The complete original Q pair and the two genuinely filed one-name
fields on their common Wilson path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQMeasuredCut
open Set Function Filter MeasureTheory Lattice Wilson RG Marker Cells QuadraticLocal
open OPE.Therm QLocalPhysicalPathKernel WilsonPositionOriginalDressedQFailedPath
open Source Labels FVA1 LocalComparison ComparisonDensity.Address
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.Replicums
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open WilsonMacroscopicForwardTransfer WilsonPositionOriginalDressedQCohortSource
open Push.GridApprox WilsonPositionOriginalDressedQLiteralLamp WilsonPositionOriginalDressedQCutSquare
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){B:MS.Local.Physical.Deck G}{p i n:ℕ}{hn:n  ≤  i+1}{V:Type}
  [DecidableEq V][Fintype V][Nonempty V](Q:MS.Land.Prescription B)
  (D:ActualRunQlocalNativeTuple.Datum R p (i+1) n hn V)(u:V→MS.Rake.Label B)(μ:ℝ)(orders:V→ℕ)
  {T I:Type}(test:T → TestSpace (ActualRunQlocalNativeTuple.orbit D))(simple:G.Simple){N:ℕ}(live:i<N)
local notation "Γ" => (Stock.census V)
local notation "Ψ" => (R.family.path.rep N p i)
local notation "S" => (R.family.path.levels.clock.op i p)

local notation "Y" => (WilsonPositionOriginalDressedQElectedPair.table R Q D u μ orders test simple live)
local notation "q" => (fun t=>letter R Q D u μ orders (test t))
variable {o:V→Site (R.family.side i p)}{P:Rep G (R.family.side i p)}
  {w:V→ℝ}{k r reg hard:ℝ}(L:QuadraticLocal.Lamps T I G P.p o (Stock.census V))
local notation "ℒ" => (WilsonRootedKioskOccupiedSlip.bare L)

def Read (B₀ periodCut:ℕ)(error maximum low:ℝ):Prop:=
  ∃ r reg:ℝ,r ≤ maximum ∧ reg ≤ low ∧
  ∃ Z:WilsonRootedKioskSealedPost.Return P o Γ w k r reg hard ℒ Y,
  ∀(a b:V),a≠b → ∀s:(Γ).Mode,s.val={a,b} → ∀(t:T),let m:=periodCut
    
    2*(m*(4*B₀+2)+2*B₀)<separation (o a) (o b) →
    let arm(v:V):=short L B₀ m ((Γ).fire v) t
    let step:=backTo R.family.path N p (Nat.le_succ i)
    ‖(∫U,((q) t a U-step (arm a) U)*((q) t b U-step (arm b) U) ∂scene R.family.path N p (i+1))-
      (∫W,(Z.output.density t W).part s/(P.eval W:ℂ) ∂scene R.family.path N p i)‖ ≤ 
      error
end YM.Integration.WilsonPositionOriginalDressedQMeasuredCut

/-! The common physical and independently published Q post. Preserve its
one elected voter and rooted full-group wallet before sealing the income. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQShortAppointment
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
  (u:V → MS.Rake.Label B) (μ:ℝ) (extra:V → ℕ) (w:V → ℝ) {ψ:ℕ → ℕ}
  (root:PlanV.Roots («G»:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (seat:root.Tab R.rolls) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit root seat)
  (posted:Spill.Raffle.Warm G root R.alloy.delay ψ)
  (income:WilsonMovingMentorRootRadius.Income («M»:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll («R»:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

variable (books:Mentor.Offices.Books root R.rolls seat ψ) (forecast:Mentor.Forecast root R.rolls seat ψ books)
  (education:Mentor.Educated root R.rolls seat R.kit.shape R.kit.scout ψ books R.alloy.delay)
  (active:∀j,MintClock.Employment root ψ j (R.rolls.L j))
  (calendar:MintClock.Regency root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (hospital:MintClock.Hospital root R.rolls seat R.kit.target ψ books forecast R.alloy.delay)
  (pass:Pass root seat R.alloy R.kit)

include income way ticket posted active calendar hospital education pass
theorem original (K grade q target tailOrder:ℕ) (ranked:rank    ≤    grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε):
    ∃ C:ℝ,1    ≤    C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop,
    ∀ (op:Mentor.Opportunity (J₀ (m+1)) (J₀ m))
      (epoch:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) op),
    op.count=h  →  op.stage=grade+1  →  epoch.vac=grade+v+h  → 
    let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
    4    ≤    Ω ∧ Ω    ≤    (β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
    ∀ (N p:ℕ) (o:V → Site (R.family.side (m+1) p)) (orders:V → ℕ), (∀i,orders i    ≤    K)  → 
      ∀ (before:m<N) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (H:(s:ℕ) → Rep G (R.family.side s p))
      (first:ℕ) (_start:first    ≤    m) (_course:Concourse R.alloy R.kit R.T π Γ first N p epoch.vac H)
      (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
      (journey:PlanV.Journey root R.alloy («N»:=N) («m»:=m) card), π (m+1)=card.extra  → 
      Topline (H N) (R.family.path.levels.clock.forcedAllowance N)  → 
      (H (m+1)).beta=(R.family.path.rep N p (m+1)).beta →
      (H m).eval=(R.family.path.rep N p m).eval →
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon (grade+v+h)) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let weights:=fun j=>w j/(a*Ω)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      (∀ s:(Stock.census V).Mode,Poly.toll weights s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1)    ≤    ε*g^q) ∧
      ∃ voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1)))
        grade op.count op.stage epoch.vac (J₀ m),
      let size:=(R.alloy.B.a.S.oneStep m p).exact_size
      let panel:=Pane.panel R.alloy m size
      let published:=Mentor.Cruise.publish root R.rolls seat R.alloy ψ books op epoch size X grade voter card
      let receipt:=Mentor.Cruise.funded root R.rolls seat R.alloy ψ books op epoch size X grade voter card journey forecast
      let E:=Mentor.Cruise.Semester.figure root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
      let L:=Width.treasured X panel.ratio published receipt (H m).p E.afterwards (Coat.gStep (H (m+1)).beta)
      (∀j,0<weights j) ∧
      WilsonRootedKioskOccupiedSlip.Gross L weights (H m).p.B ((H m).p.supportExponent+1)
        ((Spill.allOver (H m).p)^E.cap*Ω) ∧
      ∀ (_y:tastes D) (k e:ℝ),0<e  →  e   ≤   1  → 
        WilsonPositionOriginalDressedQMeasuredCut.Read R Q D u η orders
          (testInclusion (ActualRunQlocalNativeTuple.orbit D)) hG before L (w:=weights) (k:=k)
          (hard:=Time.quoteHard R.alloy.B.a m R.kit.book (H (m+1)).beta)
          (H m).p.B (Pressure.radiusB (β̂ (m+1))) ((β̂ (m+1))^tailOrder)⁻¹
          (max (max 1 k) (Ω^5+(Spill.allOver (R.alloy.B.a.budget m))^E.cap*Ω/
            Willow.haloSlack (R.alloy.B.a.budget m).B))
          (8*Ω*(e+Burn.young (β̂ (m+1)) epoch.vac +
            (Pressure.betaF G (β̂ m) (R.rolls.L (J₀ (m+1))))^Mentor.Tuition.need grade (Mentor.Tolerance (J₀ m)))) := by
  obtain ⟨C,cp,b,M,mp,D₀,book⟩:=WilsonPositionOriginalDressedQPaidAppointment.original R hG J Q u μ extra w root seat way ticket posted income
    books forecast education active calendar hospital pass K grade q target ranked positive εpos
  let A:=R.alloy.B.a
  have rise:Tendsto A.clock.hatBeta atTop atTop:=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have upperRise:Tendsto (fun m=>β̂ (m+1)) atTop atTop:=rise.comp (tendsto_add_atTop_nat 1)
  have clock:=WilsonPositionOriginalDressedQCutClock.event w positive C cp M mp.le b (grade+v+1) D₀ tailOrder
  refine ⟨C,cp,b,?_⟩
  filter_upwards [book,WilsonRootedKioskPostRadius.original R hG,upperRise.eventually clock] with m enrolled money decay
  intro op epoch count level vac Ω
  obtain ⟨ol,ou,offer⟩:=enrolled op epoch count level vac
  refine ⟨ol,ou,?_⟩
  intro N p o orders cap before π Γ H first start course card journey upper top hot coarse D σ η X a weights g
  obtain ⟨cancel,voter,paid⟩:=offer N p o orders cap before π Γ H first start course card journey upper top hot coarse
  refine ⟨cancel,voter,?_⟩
  intro size panel published receipt E lamps
  obtain ⟨hw,gross,sales⟩:=paid
  refine ⟨hw,gross,?_⟩
  have one:1  ≤  β̂ m:=money.1
  have xy:β̂ m  ≤  β̂ (m+1):=money.2.1
  have oo:1  ≤  Ω:=by linarith only [ol]
  have oy:Ω  ≤  β̂ (m+1):=by
    have grain:Beaming.grain (J₀ m) ≤ 1:=by
      unfold Beaming.grain
      exact (div_le_one (by positivity : 0<(J₀ m:ℝ)+1)).mpr (by linarith only [Nat.cast_nonneg (α:=ℝ) (J₀ m)])
    exact ou.trans ((Real.rpow_le_rpow_of_exponent_le (one.trans xy) grain).trans_eq (Real.rpow_one _))
  have sameBudget:(H m).p=R.alloy.B.a.budget m:=(course.1.walk m start before.le).truep.point
  have capValue:E.cap=grade+v+1:=rfl
  let d:ℝ:=(Spill.allOver (H m).p)^E.cap*Ω
  have dpos:0 ≤ d:=mul_nonneg (pow_nonneg (le_trans zero_le_one (Spill.allOver_ge _)) _) (zero_le_one.trans oo)
  have cost:d  ≤  (β̂ (m+1))^(grade+v+1)*Ω:=by
    dsimp only [d];rw [capValue,sameBudget]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (Spill.allOver_ge _)) (money.2.2.1.trans xy) _) (zero_le_one.trans oo)
  have toll:=decay (β̂ m) Ω ((H m).p.supportExponent+1) d one xy oo oy
    (by linarith only [(H m).p.exponent_pos]) dpos cost weights hw (fun s=>(cancel s).1)
  intro y k e ep ef
  obtain ⟨r,reg,hr,hreg,Z,hearing⟩:=sales y k e ep ef
  refine ⟨r,reg,hr,hreg,Z,?_⟩
  intro v₁ v₂ ab mode roots test radius distant
  exact (hearing v₁ v₂ ab mode roots test radius distant).trans (toll _ _ _)

end YM.Integration.WilsonPositionOriginalDressedQShortAppointment
