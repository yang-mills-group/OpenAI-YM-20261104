import YM.Integration.WilsonOriginalAlternativeFiniteSource
import YM.QuadraticLocal.Class.Registration

/-! Independently declared cutoff labels enter the same original marked school. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeFiniteSchool
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open ConnectedActivityE6 Integration.LocalComparison Mentor Advent.Sycamore
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {V:Type} [Fintype V] [DecidableEq V]
variable {G:Gauge} (R:Run G) (d:V→ℕ) (positive:∀j,0<d j) {m per k i:ℕ}
  (y:∀j,R.family.book.Ref (d j))
  (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (opened:m ≤ (i+1))
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k) (w:V→ℝ)
  (o:Positions (V) (R.family.side (i+1) per))
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => WilsonOriginalAlternativeFiniteSource.words R d positive (i+1) per y o.origin σ₀
local notation "S₀" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (V)
local notation "E₀" => Passport.point o.origin

include hk history scroll chamber opened warm top in
theorem original {c:ℝ} (unit:c≤1) (stock:Scene.Armada M₀ w d σ₀ c school.order school.pieces school.horizon)
    (test:Tableau S₀ WilsonOriginalAlternativeFiniteSource.disks M₀) (width:Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+1))
    (refs:∀j,R.family.ref (d j) ≤ (i+1)) :
    ∃ Z:Tint.Incoming E₀ P₀ (Wallet WilsonOriginalAlternativeFiniteSource.disks) Empty J₀,
      (Z.old.Paid w (P₀).p.B ((P₀).p.supportExponent+1+1) 0 ∧
       Z.hard.Paid w (P₀).p.B (P₀).p.supportExponent (forcedDivisor R.family (i+1))) ∧
      Taut (E₀).support WilsonOriginalAlternativeFiniteSource.disks S₀ Z.old ∧ Crown (E₀).support WilsonOriginalAlternativeFiniteSource.disks S₀ Z.hard ∧
      ∀ x U, (Tint.Patrol.picture M₀ Z).density x U =
        WilsonOriginalAlternativeFiniteSource.offer R d (i+1) per y o.origin x U := by
  obtain ⟨Z,earned⟩:=Boot.launching R hk D Q π Γ Ψ history scroll books chamber opened le_rfl
    WilsonOriginalAlternativeFiniteSource.disks S₀ w d school M₀ (stock.higher unit) test warm top 0 width
  refine ⟨Z,⟨Spill.Foundry.empty_lit (P₀) Z _ _ (w:=w),?_⟩,earned.clothes.seeds,earned.clothes.supplementary,?_⟩
  · simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] using earned.crown
  · intro x U
    let entry:=history.1.walk (i+1) opened le_rfl
    have same:Pert.Asymptotics.regulatorRun R.family (i+1) per (i+1)=Coat.gStep (P₀).beta :=by
      rw [entry.beta]
      rfl
    rw [(earned.face x U).2.2,←same]
    apply Eq.trans _ (WilsonOriginalAlternativeFiniteSource.entered R d positive (i+1) per y o.origin refs σ₀ x U)
    exact congrArg (fun z:ℝ=>(z:ℂ) • Poly.pass (Spill.Foundry.uncut M₀
      (Pert.Asymptotics.regulatorRun R.family (i+1) per (i+1)) x U)) (congrFun entry.view U)

end YM.Integration.WilsonOriginalAlternativeFiniteSchool
