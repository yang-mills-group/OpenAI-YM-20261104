import YM.Integration.WilsonRootedKioskPhysicalQPost
import YM.Integration.WilsonRootedKioskPostRadius

/-! Coefficient withdrawal at the original physical marker weights across the
entire occupied intake and both real kiosk mergers. The coupling price is set
before the period and applies to every signed mode of the actual output. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRootedKioskPhysicalQExchange
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

private def height (cap:ℕ):ℕ:=max 5 (cap+2)
private def multiplier (cap slots:ℕ):ℝ:=(2:ℝ)^(slots+height cap*slots)

private lemma paid {g y κ A ε:ℝ} {cap slots l p q:ℕ}
    (gp:0 ≤ g) (kp:1 ≤ κ) (cut:κ ≤ 2*y^(height cap)) (ranks:l ≤ slots)
    (ep:0 < ε) (first:A^l*g^p ≤ (ε/multiplier cap slots)*g^q)
    (temperature:g^(2*(height cap*slots))*y^(height cap*slots) ≤ (2:ℝ)^(height cap*slots)):
    (A*κ)^l*g^(p+2*(height cap*slots)) ≤ ε*g^q := by
  have extra : κ^l*g^(2*(height cap*slots)) ≤ multiplier cap slots := by
    calc
      _ ≤ (2*y^height cap)^slots*g^(2*(height cap*slots)) :=
        mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ kp ranks).trans
          (pow_le_pow_left₀ (zero_le_one.trans kp) cut slots)) (pow_nonneg gp _)
      _ = (2:ℝ)^slots*(g^(2*(height cap*slots))*y^(height cap*slots)) := by
        rw [mul_pow,←pow_mul];ring
      _ ≤ (2:ℝ)^slots*(2:ℝ)^(height cap*slots) := mul_le_mul_of_nonneg_left temperature (by positivity)
      _ = multiplier cap slots := (pow_add ..).symm
  have positive : 0 < multiplier cap slots := by unfold multiplier;positivity
  calc
    _ = (A^l*g^p)*(κ^l*g^(2*(height cap*slots))) := by rw [mul_pow,pow_add];ring
    _ ≤ ((ε/multiplier cap slots)*g^q)*multiplier cap slots := mul_le_mul first extra
      (mul_nonneg (pow_nonneg (zero_le_one.trans kp) _) (pow_nonneg gp _))
      (mul_nonneg (div_nonneg ep.le positive.le) (pow_nonneg gp _))
    _ = ε*g^q := by field_simp

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
      ∃ voter:Mentor.Cruise.Voter X (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (J₀ (m+1)))
        grade op.count op.stage epoch.vac (J₀ m),
      let size:=(R.alloy.B.a.S.oneStep m p).exact_size
      let panel:=Pane.panel R.alloy m size
      let published:=Mentor.Cruise.publish root R.rolls seat R.alloy ψ books op epoch size X grade voter card
      let receipt:=Mentor.Cruise.funded root R.rolls seat R.alloy ψ books op epoch size X grade voter card journey forecast
      let E:=Mentor.Cruise.Semester.figure root R.rolls seat R.alloy R.kit ψ books op epoch grade forecast v
      let model:=WilsonRootedKioskOccupiedSlip.bare
        (Width.treasured X panel.ratio published receipt (H m).p E.afterwards (Coat.gStep (H (m+1)).beta))
      let whole:=fun z=>panel.push (H (m+1)).beta
        ((ActualOriginalQInput.input Q D u η orders hG N before).leaf
          (testInclusion (ActualRunQlocalNativeTuple.orbit D) z)).density
      ∀ (_y:tastes D) (e:ℝ),0<e → e ≤ 1 →
        ∃ κ fee:ℝ,κ ≤ 2*(β̂ (m+1))^(max 5 (grade+v+3)) ∧
          fee ≤ 8*Ω*(e+Burn.young (β̂ (m+1)) epoch.vac +
            (Pressure.betaF G (β̂ m) (R.rolls.L (J₀ (m+1))))^Mentor.Tuition.need grade (Mentor.Tolerance (J₀ m))) ∧
          ∃ Z:WilsonRootedKioskSealedPost.Return (H m) (panel.ratio.parent ∘ (paper D u).origin)
            (Stock.census V) weights 1 κ fee (Time.quoteHard R.alloy.B.a m R.kit.book (H (m+1)).beta)
            model whole,
          (∀ z U,(Z.output.density z U).part (Stock.census V).quiet=((R.family.path.rep N p m).eval U:ℂ)) ∧
          ∀ s:(Stock.census V).Mode,
            Poly.toll (Stoop.radius weights κ) s*(a*Ω*κ)^s.val.card=Poly.toll w s ∧
            (a*Ω*κ)^s.val.card*g^(q+2*((b+1)*h)+1+2*((max 5 (grade+v+3))*h)) ≤ ε*g^q := by
  have positiveFee : 0 < multiplier (grade+v+1) h := by unfold multiplier; positivity
  obtain ⟨C,cp,b,price⟩:=WilsonRootedKioskPhysicalQPost.original R hG J Q u μ extra w root seat way ticket
    posted income books forecast education active calendar hospital pass K grade q target ranked positive
    (div_pos εpos positiveFee)
  refine ⟨C,cp,b,?_⟩
  filter_upwards [price,WilsonRootedKioskPostRadius.original R hG] with m salary cuts
  intro op epoch count level vac Ω
  obtain ⟨four,roof,meeting⟩:=salary op epoch count level vac
  refine ⟨four,roof,?_⟩
  intro N p o orders bounded before π Γ H first start course card journey upper top D σ η X a weights g
  obtain ⟨early,vote,issued⟩:=meeting N p o orders bounded before π Γ H first start course card journey upper top
  refine ⟨vote,?_⟩
  intro size panel published receipt E model whole y e ep ef
  obtain ⟨κ,fee,cut,soft,⟨Z⟩⟩:=issued y 1 e ep ef
  have cap:E.cap=grade+v+1:=rfl
  have one : 1 ≤ β̂ (m+1) := cuts.1.trans cuts.2.1
  have widen := cuts.2.2.2.2 (grade+v+1) 1 Ω (by linarith only [four]) roof
  rw [cap] at cut
  have estimate:κ ≤ 2*(β̂ (m+1))^(height (grade+v+1)) := by
    have pad:1 ≤ 2*(β̂ (m+1))^(height (grade+v+1)):=by
      have p1:1 ≤ (β̂ (m+1))^(height (grade+v+1)):=one_le_pow₀ one
      linarith only [p1]
    exact (cut.trans widen).trans (max_le ((max_le le_rfl le_rfl).trans pad) le_rfl)
  refine ⟨κ,fee,estimate,soft,Z,?_,?_⟩
  · intro z U
    exact (Z.quiet z U).trans (congrArg (fun x:ℝ => (x:ℂ)) (congr_fun (course.1.walk m start before.le).view U))
  intro s
  have zeroκ:κ≠0:= (lt_of_lt_of_le zero_lt_one Z.valid).ne'
  have restore:=WilsonRootedKioskFreeRadius.restore weights κ zeroκ s
  change κ^s.val.card*Poly.toll (Stoop.radius weights κ) s=Poly.toll weights s at restore
  constructor
  · calc
      _ = (κ^s.val.card*Poly.toll (Stoop.radius weights κ) s)*(a*Ω)^s.val.card := by rw [mul_pow];ring
      _ = _ := by rw [restore];exact (early s).1
  · have heat : g^(2*(height (grade+v+1)*h))*(β̂ (m+1))^(height (grade+v+1)*h) ≤ (2:ℝ)^(height (grade+v+1)*h) := by
      simpa only [zero_add,pow_zero,one_mul] using
        WilsonMovingMentorHardTemperature.measured R (Nat.succ_le_of_lt before) p (height (grade+v+1)*h) 0
    have gp:0 ≤ g := by dsimp only [g,Coat.gStep];positivity
    exact paid gp Z.valid estimate (Finset.card_le_univ s.val) εpos (early s).2 heat

end YM.Integration.WilsonRootedKioskPhysicalQExchange
