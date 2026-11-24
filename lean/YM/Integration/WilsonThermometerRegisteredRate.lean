import YM.Integration.WilsonThermometerRegisteredDetector
import YM.Integration.WilsonOriginalThermometerReportedToll
import YM.Integration.WilsonOriginalThermometerReportedRefund
import YM.Integration.WilsonMovingMentorPageCoupling

/-! The cost of reading an ordinary rank-six/rank-four pair after the two measured blockings. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredRate
open Finset Marker
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

/-- The two source widths together cost 108 powers and the rough singleton cofactors
cost twice their fixed physical exponent. -/
def order (p e:ℕ) := p+108+2*e

def count (t:ℕ) : ℝ := (Fintype.card (J).Mode:ℝ)*(16*(2:ℝ)^(t+1))+1

def price (r K:ℝ) (p e:ℕ) : ℝ :=
  (r*(4:ℝ)^27)^2 * count (order p e) * (1+2*K*(4:ℝ)^e+count (order p e))

private theorem afford (p e seats:ℕ) {g h y β r K Ω rent birth shrink x:ℝ}
    (gp:0 < g) (gu:g ≤ 1) (hp:0 ≤ h) (adj:h ≤ 2*g) (yp:0 ≤ y) (βp:0 ≤ β)
    (βy:β ≤ y) (band:y*g^2 ≤ 4) (rp:0 ≤ r) (kp:0 ≤ K) (fatt:0 ≤ Ω)
    (bank:Ω^seats*g^(order p e+1) ≤ g^(order p e)) (raw:rent ≤ 2*h^(order p e+1)) (rent0:0 ≤ rent)
    (cash:0 < birth) (wage:birth ≤ r*y^18) (used:1 ≤ shrink) (roof:shrink ≤ y^9)
    (w:Fin 3→ℝ) (positions:∀v,w v=birth⁻¹/shrink)
    (a b:Fin 3) (ab:a≠b) (s:(J).Mode) (both:s.val={a,b})
    (measured:Poly.toll w s*x  ≤ 
      let E:=(Fintype.card (J).Mode:ℝ)*((8*Ω^seats)*rent)+g^(order p e+1)
      E*(1+2*(K*β^e)+E)) : x ≤ price r K p e*g^p := by
  let t:=order p e
  let E:=(Fintype.card (J).Mode:ℝ)*((8*Ω^seats)*rent)+g^(t+1)
  let B:=birth*shrink
  have Bp:0 < B:=mul_pos cash (zero_lt_one.trans_le used)
  have budget:B ≤ r*y^27:=calc
    B ≤ (r*y^18)*y^9 := mul_le_mul wage roof (zero_le_one.trans used) (mul_nonneg rp (pow_nonneg yp _))
    _ = r*y^27 := by ring
  have restored:B*g^54 ≤ r*4^27 := calc
    _ ≤ (r*y^27)*g^54 := mul_le_mul_of_nonneg_right budget (pow_nonneg gp.le _)
    _ = r*(y*g^2)^27 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg yp (sq_nonneg _)) band _) rp
  have receipt:rent ≤ 2*((2*g)^(t+1)) :=
    raw.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp adj _) (by norm_num))
  have logQuote:E ≤ count t*g^t := calc
    E ≤ (Fintype.card (J).Mode:ℝ)*((8*Ω^seats)*(2*(2*g)^(t+1)))+g^(t+1) := by
      dsimp only [E]
      gcongr
    _ = ((Fintype.card (J).Mode:ℝ)*(16*(2:ℝ)^(t+1)))*(Ω^seats*g^(t+1))+g^(t+1) := by rw [mul_pow];ring
    _ ≤ ((Fintype.card (J).Mode:ℝ)*(16*(2:ℝ)^(t+1)))*g^t+g^t := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left bank (by positivity)
      · exact pow_le_pow_of_le_one gp.le gu (Nat.le_succ t)
    _ = count t*g^t := by simp [count,add_mul]
  have nonD:0 ≤ count t := by unfold count; positivity
  have Ecap:E ≤ count t := logQuote.trans (mul_le_of_le_one_right nonD (pow_le_one₀ gp.le gu))
  have fields:g^(2*e)*(1+2*(K*β^e)+E) ≤ 1+2*K*(4:ℝ)^e+count t := by
    calc
      _ = g^(2*e)+2*K*(β*g^2)^e + g^(2*e)*E := by rw [mul_pow,pow_mul]; ring
      _ ≤ 1+2*K*(4:ℝ)^e+count t := by
        apply add_le_add
        · refine add_le_add (pow_le_one₀ gp.le gu) ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg βp (sq_nonneg _))
              ((mul_le_mul_of_nonneg_right βy (sq_nonneg _)).trans band) _) (by positivity)
        · exact (mul_le_mul_of_nonneg_left Ecap (pow_nonneg gp.le _)).trans
            (mul_le_of_le_one_left nonD (pow_le_one₀ gp.le gu))
  have sqBudget:B^2*g^108 ≤ (r*4^27)^2 := calc
    _ = (B*g^54)^2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg Bp.le (pow_nonneg gp.le _)) restored _
  have toll:Poly.toll w s=B⁻¹^2 := by
    simp [Poly.toll,both,ab,positions,div_eq_mul_inv,B,sq]
    ring
  have paid:B⁻¹^2*x ≤ E*(1+2*(K*β^e)+E) := toll ▸ measured
  have earn:0 ≤ 1+2*(K*β^e)+E := by dsimp [E];positivity
  calc
    x = B^2*(B⁻¹^2*x) := by field_simp [Bp.ne']
    _ ≤ B^2*(E*(1+2*(K*β^e)+E)) := mul_le_mul_of_nonneg_left paid (sq_nonneg _)
    _ ≤ B^2*((count t*g^t)*(1+2*(K*β^e)+E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right logQuote earn) (sq_nonneg _)
    _ = (B^2*g^108)*count t*(g^(2*e)*(1+2*(K*β^e)+E))*g^p := by
      dsimp only [t,order]; rw [pow_add,pow_add];ring
    _ ≤ (r*4^27)^2*count t*(1+2*K*(4:ℝ)^e+count t)*g^p := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg gp.le _)
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right sqBudget nonD
      · exact fields 
      · exact mul_nonneg (pow_nonneg gp.le _) earn
      · exact mul_nonneg (sq_nonneg _) nonD
    _ = _ := by rfl

open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i+1)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+2) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
local notation "M₀" => primitive R A (i+2) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+2)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

open FVA1Physical.TwoReset

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)


open WilsonOriginalReceivedChain Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open WilsonThermometerCourseIntake

variable
  (strip : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q depth : ℕ) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4 ≤ 3*k+2)
  (H cap:ℝ) (cap_pos:0 ≤ cap)

open WilsonThermometerRegisteredPair OriginalForcedAddresses Extra.Trajectories
open WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading

local notation "earlier" => (show i < i+2 from by omega)
local notation "first" => (Nat.lt_succ_self (i+1))
local notation "input" => WilsonReceivedCloseHistory.history (N:=i+2) R disks (head) i (Nat.le_succ i)
local notation "second" => WilsonThermometerCourseHearing.offered R A simple (earlier) o
local notation "g₁" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "g₂" => Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
local notation "stage" => ((Advent.budgetR R i)^2*(Advent.budgetR R (i+1))^7)


open WilsonOriginalThermometerTollBudget
local notation "y" => R.family.path.levels.clock.hatBeta (i+2)
local notation "K₀" => WilsonThermometerRegisteredOrdinary.gross R simple (f:=f) (F:=F) fund slow
local notation "e₀" => WilsonThermometerRegisteredOrdinary.power R simple (f:=f) (F:=F) fund slow
local notation "crop" => (E₁)*(Ω₀)

def warmDate : ℕ := (eventually_atTop.mp
  ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2:ℝ))).choose

private theorem small (warm:warmDate R simple ≤ m) (j N per:ℕ) (mj:m ≤ j) (jn:j ≤ N) :
    0 < Coat.gStep (R.family.path.rep N per j).beta ∧ Coat.gStep (R.family.path.rep N per j).beta ≤ 1 := by
  have paid:=(eventually_atTop.mp
    ((Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2:ℝ))).choose_spec j (warm.trans mj)
  have lo:(R.family.path.levels.clock.hatBeta j)/2 ≤ (R.family.path.rep N per j).beta:=
    (R.makes.wilson.represents N per j jn).band.1
  have threshold:1 ≤ (R.family.path.rep N per j).beta := by linarith only [paid,lo]
  have beta:=Real.one_le_sqrt.mpr threshold
  exact ⟨inv_pos.mpr (zero_lt_one.trans_le beta),inv_le_one_of_one_le₀ beta⟩

def priceDate (target e:ℕ) : ℕ := max
  (eventually_atTop.mp (WilsonOriginalThermometerRefund.measured R simple)).choose
  (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple school.pieces
    (order target e) (ε:=1) zero_lt_one)).choose

include history scroll chamber warm top cal hospital fund slow in
/-- The ordinary two-field hearing costs a fixed power determined by the two true reported
sources. For each requested order the constant and all delay tests precede the period and positions. -/
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (opStage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ v,R.family.ref (levels v) ≤ i+2)
    (floor:m ≤ i) (fit:k ≤ R.alloy.B.a.clock.J i)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:school.order ≤ Burn.horizon k+1) (shelved:school.horizon ≤ R.alloy.B.a.clock.J m)
    (load:school.pieces ≤ Burn.horizon k+2) (packed:school.order+school.horizon ≤ Burn.horizon k+2)
    (tender:WilsonReceivedMeasuredStampPrice.opening R simple q school.order k
      (show 2*q+8 ≤ school.order from by omega) (show q+3 ≤ 3*k+2 from by omega) zero_lt_one ≤ m+1)
    (held:0 < i) (fieldDate:WilsonThermometerRegisteredOrdinary.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (heard:WilsonThermometerRegisteredPair.opening R simple D school strip q depth deep aged H cap cap_pos
      (ε:=1) zero_lt_one ≤ i)
    (orderWanted:ℕ) (surplus:q=order orderWanted (e₀)+1)
    (heat:warmDate R simple ≤ m) (funded:priceDate R simple school orderWanted (e₀) ≤ i)
    (rootFee:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (stencil:reach R ≤ R.alloy.B.a.clock.J (i+2)+1) :
      ∀ t a b:Fin 3, a≠b → a≠t → b≠t → ∀ link:Stationary.Link G (R.family.side i per),
      let B:=R.family.path.levels.budget i
      let β:=R.family.path.levels.clock.hatBeta i
      let angle:=Stationary.arm G (R.family.side i per) 1 link
      ∀ z:ℝ, |z| ≤ |H| * (Real.log β)^depth * ((B.B:ℝ)^2*B.threshold)/g₁ →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap * |z|) →
        let W:=Integral.sample g₁ angle
        flags (Ψ i).p.threshold W=∅ →
        let fields:=fun v:Fin 3 => R.family.O (i+2) per
          (A.station.wheel.atCut (i+2,per) (index A (grade v)) (vector A univ v)) (o.origin v)
        let two:=actualTransport R.family (N:=i+2) (fun U=>fields a U*fields b U) (earlier).le W
        let bare:=WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o (without t)
        let formal:=WilsonOriginalCoveredEvolution.run R first π Γ (Burn.horizon k+2) school.order levels bare
        let target:=WilsonCoherentMayerWindingGrades.panel school.order (g₁:ℂ)
          (fun e=>formal i (Nat.le_succ i) _ (dvd_refl _) e link)
        let s:(J₀).Mode:=⟨{a,b},mem_univ _⟩
        ‖two-(target.part s+target.part ((J₀).fire a)*target.part ((J₀).fire b))‖ ≤
          price (rate R) (K₀) orderWanted (e₀) * g₁^orderWanted := by
  have little:=small R simple heat
  have cash:=little (i+2) (i+2) per (by omega) le_rfl
  have rp:0 < g₂^q:=pow_pos cash.1 _
  have nearOne:g₂^q ≤ 1:=pow_le_one₀ cash.1.le cash.2
  obtain ⟨P,d,d₁,dk,weights,bill,ordinary⟩:=WilsonThermometerRegisteredDetector.original R simple A
    hk D Q π Γ Ψ history scroll books chamber hi warm top school o op lesson cal ahead hospital
    fund slow strip q depth deep aged H cap cap_pos (ε:=1) zero_lt_one late date checked near shape
    size space room opStage ranks width refs rp nearOne floor fit path pass month fits shelved load packed
    le_rfl tender held fieldDate heard (fun j mj jN=>little j (i+2) per mj jN)
  obtain ⟨U,_,_,_,_,_,_,opEq,lessonEq,_,_,_,_⟩:=WilsonThermometerRegisteredStation.original R simple A
    hk D Q π Γ Ψ history scroll books chamber hi warm top school o op lesson cal ahead hospital
    fund slow late date checked near shape size space room opStage ranks width refs rp nearOne
  have budget:Ω₀ ≤ Advent.budgetR R (i+1):=by simpa only [opEq,lessonEq] using U.issued.Beamwork
  have top0 : 0 < Ω₀ := zero_lt_one.trans_le
    ((by norm_num : (1:ℝ) ≤ 4).trans (MintClock.Page.roofers ..))
  have before:=WilsonOriginalThermometerReportedToll.original R simple D φ rootFee i (Burn.horizon k)
    (((Nat.le_add_right _ _).trans hk).trans (R.alloy.B.a.fits.mono (by omega : m ≤ i+2)))
    stencil top0.le budget
  have wage:crop ≤ rate R*y^18 := before
  have originalField:0 < crop := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) top0
  have yp : 1 ≤ y := (R.alloy.B.a.fits.delayed (i+2)).le
  have rise (j:ℕ):R.family.path.levels.clock.hatBeta j ≤ R.family.path.levels.clock.hatBeta (j+1) :=
    WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le (Nat.le_succ j)
  have budget0:Advent.budgetR R i ≤ y := (parameter R i).trans (rise (i+1))
  have budget1:Advent.budgetR R (i+1) ≤ y := parameter R (i+1)
  have roof:d ≤ y^9:=dk.trans (calc
    (Advent.budgetR R i)^2*(Advent.budgetR R (i+1))^7 ≤ y^2*y^7 := by
      exact mul_le_mul
        (pow_le_pow_left₀ (zero_le_one.trans (Advent.budget_pos R)) budget0 2)
        (pow_le_pow_left₀ (zero_le_one.trans (Advent.budget_pos R)) budget1 7)
        (pow_nonneg (zero_le_one.trans (Advent.budget_pos R)) _)
        (sq_nonneg _)
    _ = y^9 := by ring)
  obtain ⟨gp,gu,band,_⟩:=(eventually_atTop.mp (WilsonOriginalThermometerRefund.measured R simple)).choose_spec i
    ((le_max_left ..).trans funded) per
  let Ω:=Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead school.order school.horizon
  have Ωp : 0 ≤ Ω := zero_le_one.trans P.issued.Waffle.cool
  have bank:Ω^school.pieces*g₁^(order orderWanted (e₀)+1) ≤ g₁^(order orderWanted (e₀)):=by
    simpa only [one_mul] using (eventually_atTop.mp (WilsonMovingMentorPageCoupling.repaid R simple
      school.pieces (order orderWanted (e₀)) (ε:=1) zero_lt_one)).choose_spec i
      ((le_max_right ..).trans funded) Ω Ωp (P.issued.Beamwork.trans (min_le_right ..)) (i+2) per earlier
  have returns:P.rent ≤ 2*g₂^(order orderWanted (e₀)+1):=by simpa only [one_mul,←two_mul,surplus] using bill
  have kg:0 ≤ K₀:=zero_le_one.trans
    (WilsonOriginalThermometerReportedFaces.leg R (f:=f) (H:=F) simple fund slow).choose_spec.1
  intro t a b ab at' bt' link B β angle z zpos fitsz W healthy fields two bare formal filed s
  have paid:=ordinary t a b ab at' bt' link z zpos fitsz healthy
  apply afford orderWanted (e₀) school.pieces gp gu cash.1.le
    (WilsonLocalCompactRichPortUnits.compared R simple (by omega : i+1 ≤ i+2) (le_refl _) per)
    (zero_le_one.trans yp) (show 0 ≤ R.family.path.levels.clock.hatBeta i from
      zero_le_one.trans (R.alloy.B.a.fits.delayed i).le)
    ((rise i).trans (rise (i+1))) band (zero_le_one.trans (le_max_left _ _)) kg Ωp bank returns P.active.le
    originalField wage d₁ roof P.w weights a b ab s rfl
  simpa only [one_mul,surplus,Ω,mul_assoc,s,two,fields,filed,formal,bare,W,angle,B] using paid

end YM.Integration.WilsonThermometerRegisteredRate
