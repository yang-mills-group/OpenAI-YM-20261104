import YM.Integration.WilsonReceivedCloseCoissuedFunding
import YM.TraceExtension.Atlas.Global

/-! The complete two-appointment physical Q post on the regulator filter of
the selected physical field hierarchy. The post is issued before the two
sets of sites or derivative orders are chosen. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissQPost
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
open Pert.Asymptotics Extra.Histories WilsonOriginalReceivedChain
open scoped Classical BigOperators
open VowsR QuadraticLocal.Affinity Sycamore
variable {G:Gauge} (R:Run G) (simple:G.Simple)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  {φ:ℕ→ℕ} (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books) {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:Treehouse.VariableHouse R D Q scroll books ZΘ ahead profile)
  (protection:WilsonPhysicalHistoryPriorAperture.Paid R.rolls D φ R.alloy.delay)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
  (hire:∀d,MintClock.Employment D φ d (R.rolls.L d))
  {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (request upperJ:Request V) (freshQ upperQ:MS.Land.Prescription B)
  (u upperLabels:V→MS.Rake.Label B) (μ upperClock:ℝ) (extra upperExtra:V→ℕ)
  (K upperOrder:ℕ) (old fresh:Finset V) (sep:Disjoint old fresh)
local notation "axes" => Fintype.card V
local notation "uGrade" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels
local notation "lGrade" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "roomSize" => axes*uGrade
local notation "rank" => max (ActualOriginalQLayout.rankCap R upperLabels) (ActualOriginalQLayout.rankCap R u)
local notation "ch" => house.licence.employed
local notation "d₀" => WilsonReceivedCloseQNamedSalary.degree R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
local notation "currency" => WilsonReceivedCloseQNamedSalary.currency R simple request freshQ u μ extra D income K Q
  books ahead (ch).ready (ch).station house.stamps (ch).education hire house.calendar house.licence.forecast
  (ch).station.1 upperJ upperQ upperLabels upperClock upperExtra upperOrder
variable (comparison span shape:ℕ) (height angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "target" => comparison+1+((2*d₀+1)*axes+1)+axes
local notation "prec₀" => WilsonReceivedCloseQSchool.precision (d₀) axes (target)
local notation "p₁" => WilsonReceivedCloseQSchool.precision (d₀) axes ((target)+1)
local notation "o₀" => WilsonReceivedCloseQSchool.degree (d₀) axes (rank) ((target)+1)
local notation "k₀" => WilsonReceivedCloseQSchool.vacuum (d₀) axes (rank) (roomSize) ((target)+1)
local notation "Sch" => WilsonReceivedCloseQSchool.school (d₀) axes (rank) (roomSize) ((target)+1)
local notation "opAt" j:max h:max => (Sch).room (Push.PriceCompiler.step_paid R.alloy.B.a (j+1)) h
local notation "sales" => WilsonReceivedCloseQSchool.resources (d₀) axes (rank) (roomSize) ((target)+1)

def At (l:Ultrafilter (ℕ×ℕ)) : Prop :=
  ∀ᶠ m:ℕ in atTop,∀ j (floor:m≤j),PaceR.Close R shape cap m j →
    ∀ᶠ z:ℕ×ℕ in (l:Filter (ℕ×ℕ)),let N:=z.1; let per:=z.2; ∃ (cut:j+1<N),
      ∃ (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (hk:Burn.horizon (k₀)+2 ≤ R.alloy.B.a.clock.J m)
      (_lesson:Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))),
      PlanV.Path D R.alloy Q (Burn.horizon (k₀)) N m π Γ ∧
      ∃ Ψ:∀l,RG.Rep G (R.family.side l per),Concourse R.alloy R.kit R.T π Γ m N per (k₀) Ψ ∧
        Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
        ∀ (upperSites:V→Site (R.family.side ((j+1)+1) per)) (sites:V→Site (R.family.side (j+1) per))
          (upperOrders orders:V→ℕ), (∀v,upperOrders v≤upperOrder) → (∀v,orders v≤K) →
          WilsonReceivedCloseQCoissued.Receipt (R:=R) (simple:=simple) (request:=request) (freshQ:=freshQ)
            (u:=u) (μ:=μ) (extra:=extra) (D:=D) (income:=income) (K:=K) (hk:=hk) (Q:=Q) (π:=π)
            (Γ:=Γ) (Ψ:=Ψ) (books:=books) (floor:=floor) (cut:=cut)
            (op:=opAt j (hk.trans (R.alloy.B.a.fits.mono (floor.trans (Nat.le_succ j)))))
            (ahead:=ahead) (way:=(ch).ready) (ticket:=(ch).station) (warm:=house.stamps)
            (education:=(ch).education) (employment:=hire) (calendar:=house.calendar) (hospital:=house.licence.forecast)
            (pass:=(ch).station.1) (upperJ:=upperJ) (upperQ:=upperQ) (upperLabels:=upperLabels) (upperClock:=upperClock)
            (upperExtra:=upperExtra) (upperOrder:=upperOrder) (order:=o₀) (shelf:=roomSize)
            (upperSites:=upperSites) (upperOrders:=upperOrders) (sites:=sites) (orders:=orders)
            (old:=old) (fresh:=fresh) (span:=span) (height:=height) (angleCap:=angleCap)
            comparison ε

theorem filed {f:Extraction.Order} {l:Ultrafilter (ℕ×ℕ)} (inside:(l:Filter (ℕ×ℕ))≤f.fuse)
    (heard:WilsonReceivedCloseQCoissuedProgram.Heard R simple D Q scroll books ahead house income hire
      request upperJ freshQ upperQ u upperLabels μ upperClock extra upperExtra K upperOrder old fresh
      comparison span shape height angleCap cap ε):
    At R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels μ upperClock
      extra upperExtra K upperOrder old fresh comparison span shape height angleCap cap ε l:=by
  filter_upwards [heard] with m hm
  intro j floor close
  filter_upwards [(Trace.Terrace.link_mesh inside).eventually_ge_atTop (j+2)] with z top
  obtain ⟨π,Γ,hk,lesson,path,all⟩:=hm j floor close z.1 top
  exact ⟨top,π,Γ,hk,lesson,path,all z.2⟩

def Booked (l:Ultrafilter (ℕ×ℕ)) : Prop :=
  ∀ {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (request upperJ:Request V) (freshQ upperQ:MS.Land.Prescription B)
    (u upperLabels:V→MS.Rake.Label B) (μ upperClock:ℝ) (extra upperExtra:V→ℕ)
    (K upperOrder:ℕ) (old fresh:Finset V) (_sep:Disjoint old fresh)
    (comparison span shape:ℕ) (height angleCap cap ε:ℝ),
    0≤angleCap → 0≤cap → 0<ε →
    old∪fresh=univ →
    gradeTotal old (fun _:V=>WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels)
      (fun _:V=>WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u) ≤
      Fintype.card V*WilsonOriginalProjectedCurvatureLoan.toll (R:=R) upperLabels →
    At R simple D Q scroll books ahead house income hire request upperJ
      freshQ upperQ u upperLabels μ upperClock extra upperExtra K upperOrder old fresh comparison span
      shape height angleCap cap ε l

theorem on_course {f:Extraction.Order} {l:Ultrafilter (ℕ×ℕ)} (inside:(l:Filter (ℕ×ℕ))≤f.fuse)
    (issued:WilsonReceivedCloseCoissuedFunding.Given R simple D Q scroll books ahead house income hire):
    Booked R simple D Q scroll books ahead house income hire l:=by
  intro B V _ _ _ request upperJ freshQ upperQ u upperLabels μ upperClock extra upperExtra K upperOrder old fresh
    disjoint comparison span shape height angleCap cap ε hp cp ep whole grades
  exact filed R simple D Q scroll books ahead house income hire request upperJ freshQ upperQ u upperLabels μ
    upperClock extra upperExtra K upperOrder old fresh comparison span shape height angleCap cap ε inside
    (issued request upperJ freshQ upperQ u upperLabels μ upperClock extra upperExtra K upperOrder old fresh disjoint
      comparison span shape height angleCap cap ε hp cp ep whole grades)

end YM.Integration.WilsonOriginalBlissQPost
