import YM.Integration.WilsonOriginalThermometerTopDensity
import YM.QuadraticLocal.Class.Registration

/-! The registered grade-six/four/four birth on the original measured course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerSchoolIntake
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open ConnectedActivityE6 Integration.LocalComparison Mentor Advent.Sycamore
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (opened:m ≤ (i+1))
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k) (w:Fin 3→ℝ)
  (o:Positions (Fin 3) (R.family.side (i+1) per))
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => primitive R A (i+1) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin

include hk history scroll chamber opened warm top in
theorem original {c:ℝ} (unit:c≤1) (stock:Scene.Armada M₀ w levels σ₀ c school.order school.pieces school.horizon)
    (test:Tableau S₀ disks M₀) (width:Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+1))
    (refs:∀j,R.family.ref (levels j) ≤ (i+1)) :
    ∃ Z:Tint.Incoming E₀ P₀ (Wallet disks) Empty J₀,
      (Z.old.Paid w (P₀).p.B ((P₀).p.supportExponent+1+1) 0 ∧
       Z.hard.Paid w (P₀).p.B (P₀).p.supportExponent (forcedDivisor R.family (i+1))) ∧
      Taut (E₀).support disks S₀ Z.old ∧ Crown (E₀).support disks S₀ Z.hard ∧
      ∀ x U, (Tint.Patrol.picture M₀ Z).density x U =
        WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o x U := by
  obtain ⟨Z,earned⟩:=Boot.launching R hk D Q π Γ Ψ history scroll books chamber opened le_rfl
    disks S₀ w levels school M₀ (stock.higher unit) test warm top 0 width
  refine ⟨Z,⟨Spill.Foundry.empty_lit (P₀) Z _ _ (w:=w),?_⟩,earned.clothes.seeds,earned.clothes.supplementary,?_⟩
  · simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] using earned.crown
  · intro x U
    let entry:=history.1.walk (i+1) opened le_rfl
    have same:Pert.Asymptotics.regulatorRun R.family (i+1) per (i+1)=Coat.gStep (P₀).beta :=by
      rw [entry.beta]
      rfl
    rw [(earned.face x U).2.2,←same]
    apply Eq.trans _ (WilsonOriginalThermometerTopDensity.offered R A simple i per o refs σ₀ x U)
    exact congrArg (fun z:ℝ=>(z:ℂ) • Poly.pass (Spill.Foundry.uncut M₀
      (Pert.Asymptotics.regulatorRun R.family (i+1) per (i+1)) x U)) (congrFun entry.view U)

end YM.Integration.WilsonOriginalThermometerSchoolIntake
