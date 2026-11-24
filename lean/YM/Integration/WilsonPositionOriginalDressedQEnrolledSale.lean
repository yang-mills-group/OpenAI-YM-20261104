import YM.Integration.WilsonRootedKioskMeasuredCourse
import YM.Integration.WilsonCoherentMayerMeasuredEarnings

/-! The common physical and independently published Q post. Preserve its
one elected voter and rooted full-group wallet before sealing the income. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQEnrolledSale
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
theorem original (K grade q target:ℕ) (ranked:rank  ≤  grade) (positive:∀j,0<w j) {ε:ℝ} (εpos:0<ε):
    ∃ C:ℝ,1  ≤  C ∧ ∃ b:ℕ,∀ᶠ m:ℕ in atTop,
    ∀ (op:Mentor.Opportunity (J₀ (m+1)) (J₀ m))
      (epoch:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) op),
    op.count=h  →  op.stage=grade+1  →  epoch.vac=grade+v+h  → 
    let Ω:=Mentor.Cruise.Semester.expense root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
    4  ≤  Ω ∧ Ω  ≤  (β̂ (m+1))^(Beaming.grain (J₀ m)) ∧
    ∀ (N p:ℕ) (o:V → Site (R.family.side (m+1) p)) (orders:V → ℕ), (∀i,orders i  ≤  K)  → 
      ∀ (before:m<N) (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (H:(s:ℕ) → Rep G (R.family.side s p))
      (first:ℕ) (_start:first  ≤  m) (_course:Concourse R.alloy R.kit R.T π Γ first N p epoch.vac H)
      (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
      (journey:PlanV.Journey root R.alloy («N»:=N) («m»:=m) card), π (m+1)=card.extra  → 
      Topline (H N) (R.family.path.levels.clock.forcedAllowance N)  → 
      let D:=ActualOriginalQPointSetup.pointDatum R J p (m+1) o
      let σ:=Poetry.Agenda.seed root ψ (Burn.horizon (grade+v+h)) (J₀ (m+1))
      let η:=(μ+R.family.S.scale N-R.family.S.scale (m+1))-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ (m+1))^(b+1)
      let weights:=fun j=>w j/(a*Ω)
      let g:=Coat.gStep (R.family.path.rep N p (m+1)).beta
      (∀ s:(Stock.census V).Mode,Poly.toll weights s*(a*Ω)^s.val.card=Poly.toll w s ∧
        (a*Ω)^s.val.card*g^(q+2*((b+1)*h)+1)  ≤  ε*g^q) ∧
      ∃ voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1)))
        grade op.count op.stage epoch.vac (J₀ m),
      let size:=(R.alloy.B.a.S.oneStep m p).exact_size
      let panel:=Pane.panel R.alloy m size
      let published:=Mentor.Cruise.publish root R.rolls seat R.alloy ψ books op epoch size X grade voter card
      let receipt:=Mentor.Cruise.funded root R.rolls seat R.alloy ψ books op epoch size X grade voter card journey forecast
      let E:=Mentor.Cruise.Semester.figure root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
      let L:=Width.treasured X panel.ratio published receipt (H m).p E.afterwards (Coat.gStep (H (m+1)).beta)
      let model:=WilsonRootedKioskOccupiedSlip.bare L
      (∀j,0<weights j) ∧
      WilsonRootedKioskOccupiedSlip.Gross L weights (H m).p.B ((H m).p.supportExponent+1)
        ((Spill.allOver (H m).p)^E.cap*Ω) ∧
      ∀ (_y:tastes D) (k e:ℝ),0<e  →  e ≤ 1  → 
        WilsonRootedKioskMeasuredCourse.Payout («touch»:=panel.ratio.parent ∘ (paper D u).origin)
          (H m) weights k (Time.quoteHard R.alloy.B.a m R.kit.book (H (m+1)).beta)
          (max (max 1 k) (Ω^5+(Spill.allOver (R.alloy.B.a.budget m))^E.cap*Ω/
            Willow.haloSlack (R.alloy.B.a.budget m).B))
          (8*Ω*(e+Burn.young (β̂ (m+1)) epoch.vac +
            (Pressure.betaF G (β̂ m) (R.rolls.L (J₀ (m+1))))^Mentor.Tuition.need grade (Mentor.Tolerance (J₀ m))))
          model (fun z=>panel.push (H (m+1)).beta
            ((ActualOriginalQInput.input Q D u η orders hG N before).leaf
              (testInclusion (ActualRunQlocalNativeTuple.orbit D) z)).density) := by
  obtain ⟨C,cp,b,paid⟩:=WilsonCoherentMayerMeasuredEarnings.original R hG J Q u μ extra w root seat way ticket posted income
    books forecast education active calendar hospital pass K grade q target ranked positive εpos
  refine ⟨C,cp,b,?_⟩
  filter_upwards [paid,R.alloy.B.a.fits.deep.eventually_ge_atTop v] with m issued room
  intro op epoch count level vac Ω
  obtain ⟨large,roof,available⟩:=issued op epoch count level vac
  refine ⟨large,roof,?_⟩
  intro N p o orders bounded before π Γ H first start course card journey upper top D σ η X a weights g
  obtain ⟨cancel,positiveW,vote,seated,gross,input,_prior,reads,sealedQ,file,Z,left,_week⟩:=
    available N p o orders bounded before π Γ H first start course card journey upper top
  refine ⟨cancel,vote,?_⟩
  intro size panel published receipt E lamps fullModel
  refine ⟨positiveW,gross,?_⟩
  intro y k e ep ef
  have ready:Scene.Armada X weights (fun _=>t)
      (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1))) Ω⁻¹ grade op.count v :=
    ⟨⟨fun s=>(seated.quota s).trans count.ge, seated.crew⟩,seated.positive,seated.suggests,
      ⟨seated.purchases.spend,fun i=>⟨((seated.purchases.usable i).1).trans ranked,(seated.purchases.usable i).2⟩⟩,
      seated.honor⟩
  have load:op.count ≤ Burn.horizon epoch.vac+2:=by rw [count,vac];unfold Burn.horizon;omega
  have payout:=WilsonRootedKioskMeasuredCourse.original («R»:=R) («simple»:=hG) («root»:=root) («table»:=seat)
    (ψ:=ψ) («books»:=books) («pass»:=pass) («education»:=education) («op»:=op) («epoch»:=epoch)
    («card»:=card) («journey»:=journey) («course»:=course) («start»:=start) («before»:=before)
    («M»:=X) («w»:=weights) («positive»:=positiveW) («voter»:=vote) («input»:=input) («sealed»:=sealedQ) («y»:=y)
    («forecast»:=forecast) («hospital»:=hospital) («load»:=load) («rank»:=room) («T»:=fun _=>t)
    («phase»:=ep) («full»:=ef) k (le_refl _) ready Z left file
  have original: (Tint.Patrol.picture X input).density =
      fun z => ((ActualOriginalQInput.input Q D u η orders hG N before).leaf
        (testInclusion (ActualRunQlocalNativeTuple.orbit D) z)).density := by
    funext z U
    exact reads z U
  rw [original] at payout
  exact payout

end YM.Integration.WilsonPositionOriginalDressedQEnrolledSale
