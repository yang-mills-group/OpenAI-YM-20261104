import YM.Integration.WilsonReceivedCloseCopiedThermometer

/-! All finite ordinary accuracies are enrolled on one earlier chosen run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseThreeSlotSchool
open Pert.Asymptotics
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators


variable {G:Gauge} (R:Run G)
local notation "Jm" => R.alloy.B.a.clock.J

def jetOrder (q:ℕ) : ℕ := max (WilsonOriginalStarSceneWords.maximum R levels) (2*((q+226)+1)+8)
def vacuum (q:ℕ) : ℕ := jetOrder R q+14
def school (q:ℕ) : Syl.School (vacuum R q) :=
  ⟨jetOrder R q,3,14,by unfold vacuum Burn.horizon; omega,
    by unfold vacuum Burn.horizon; omega,by unfold vacuum Burn.horizon; omega⟩

theorem degree (q:ℕ) : 2*((q+226)+1)+8 ≤ (school R q).order := Nat.le_max_right _ _
theorem allotment (q:ℕ) : q+226+4 ≤ 3*vacuum R q+2 := by
  have bound:=degree R q
  change 2*((q+226)+1)+8 ≤ jetOrder R q at bound
  unfold vacuum
  omega

def opportunity (q i:ℕ) (hp:Burn.horizon (vacuum R q)+2 ≤ Jm (i+1)) :
    Mentor.Opportunity (Jm (i+2)) (Jm (i+1)) :=
  (school R q).room (Push.PriceCompiler.step_paid R.alloy.B.a (i+1)) hp

theorem booked (q i:ℕ) (hp:Burn.horizon (vacuum R q)+2 ≤ Jm (i+1)) :
    (opportunity R q i hp).count=3 ∧ (opportunity R q i hp).stage=(school R q).order+1 :=
  ⟨rfl,rfl⟩

variable (simple:G.Simple) (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ:ℕ→ℕ)
  (protection:∀ x k:ℕ,k≤x→∀β:ℝ,R.alloy.delay.betaEntry x≤β→
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹^2)≤β)
  {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
  (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)
  (q span shape:ℕ) (H angleCap cap ε:ℝ) (hp:0≤angleCap) (cp:0≤cap) (ep:0<ε)
local notation "K₁" => vacuum R q
local notation "Sch" => school R q
local notation "reportedPrice" => WilsonReceivedCloseReportedWallet.unit R
local notation "trained" m:max i:max => WilsonReceivedCloseStationCalendar.Ready R simple D φ protection levels
  (K₁) (Sch).order (Sch).horizon (Sch).pieces 3 18 q (q+226) span shape (reportedPrice) H angleCap cap ε
  (WilsonReceivedCloseReportedWallet.covers R) (degree R q) (allotment R q) hp cp ep m (i+1)
local notation "bookable" => WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow

structure Prepared (m i:ℕ) : Prop where
  awake : Burn.horizon (K₁)+2 ≤ Jm m
  room : (Sch).horizon ≤ Jm m
  stage : (K₁) ≤ Jm m
  late : bookable ≤ i
  ranks : 6 ≤ Jm (i+1)
  width : Sycamore.Boot.need 0 (Sch) ≤ Jm (i+2)
  support : WilsonOriginalThermometerTollBudget.reach R ≤ Jm (i+2)+1
  reference : ∀v : Fin 3, R.family.ref (levels v) ≤ i+2
  windows : trained m i

/-- Choose the real school and its wage on the original run before periods or inserted field positions. -/
theorem original : ∀ᶠ m:ℕ in atTop, ∀ i, m ≤ i+1 →
    Prepared R simple D φ protection (f:=f) (F:=F) fund slow q span shape H angleCap cap ε hp cp ep m i := by
  let refs := univ.sup (fun v:Fin 3 => R.family.ref (levels v))
  have windows:=WilsonReceivedCloseStationCalendar.original R simple D φ protection levels (K₁)
    (Sch).order (Sch).horizon (Sch).pieces 3 18 q (q+226) span shape (reportedPrice) H angleCap cap ε
    (WilsonReceivedCloseReportedWallet.covers R) (degree R q) (allotment R q) hp cp ep
  filter_upwards [windows, R.alloy.B.a.fits.deep.eventually_ge_atTop (Burn.horizon (K₁)+2),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (Sycamore.Boot.need 0 (Sch)),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (WilsonOriginalThermometerTollBudget.reach R),
    eventually_ge_atTop (bookable+1),eventually_ge_atTop refs] with m openSchool awake width support late origins
  intro i opened
  have fine : m ≤ (i+2) := opened.trans (Nat.le_succ _)
  have grade : 14 ≤ K₁ := Nat.le_add_left _ _
  have large : K₁ ≤ Burn.horizon (K₁)+2 := by unfold Burn.horizon; omega
  refine ⟨awake,grade.trans (large.trans awake),large.trans awake,by omega,?_,
    width.trans (R.alloy.B.a.fits.mono fine),?_,?_,openSchool _ opened⟩
  · exact (show 6≤14 by decide).trans (grade.trans (large.trans (awake.trans (R.alloy.B.a.fits.mono opened))))
  · exact (support.trans (R.alloy.B.a.fits.mono fine)).trans (Nat.le_succ _)
  · intro v
    have bound:R.family.ref (levels v)≤refs:=le_sup (f:=fun z:Fin 3=>R.family.ref (levels z)) (mem_univ v)
    exact bound.trans (origins.trans fine)

end YM.Integration.WilsonReceivedCloseThreeSlotSchool
