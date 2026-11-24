import YM.Integration.WilsonOriginalSeparatedElection
import YM.Integration.WilsonOriginalSmallStrip

/-! Enumerate pre-length requirements before selecting the Wilson run.
The common width at a stage is independent of the individual later requests. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedCalendar
open Function Filter Finset Lattice Wilson RG RG.Supply Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonWindowJointPurchase WilsonWindowBookPurchase
open WilsonReportingAbsoluteInletSchool WilsonOriginalSeparatedElection
open OPE.Owl WilsonCoeffUV WilsonCoeffUV.Bank
open FormalBulk08 FormalBulk08.Flat Next.Foundations Push.PriceCompiler
open WilsonWindowUniversalSchool
open WilsonOriginalSmallStrip (Menu)
open scoped Classical
universe u
variable {G : Gauge} {φ : ℕ → ℕ}

def calendar (request : ℕ → Menu G) : Menu G where
  cap := fun K j H => Finset.univ.inf' Finset.univ_nonempty
    (fun k : Fin (j+1) => (request k.val).cap K j H)
  positive := fun K j H => (Finset.lt_inf'_iff _).2
    (fun k _ => (request k.val).positive K j H)
  threshold := fun K j => (range (j+1)).sup (fun n => (request n).threshold K j)
  bill := fun K j H => ∑ n ∈ range (j+1), |(request n).bill K j H|

/-- At a given date all active requests obtain the same positive strip, with
their individual length and numerical charges paid on the actual schedule. -/
def Open (request : ℕ → Menu G) (R : Run G) : Prop := ∀ i H, H ≤ R.alloy.B.a.clock.J i →
  let j := R.alloy.B.a.clock.J i
  let K := R.metals.p.kernel
  ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ Real.exp (σ⁻¹^2) ≤ R.alloy.B.a.clock.hatBeta i ∧
    ∀ n, n ≤ j → (request n).threshold K j ≤ (R.rolls.L j).val ∧
      σ ≤ (request n).cap K j H ∧ (request n).bill K j H ≤ budgetR R i

theorem opened (request : ℕ → Menu G) (R : Run G)
    (purchase : WilsonOriginalSmallStrip.Filed (calendar request) R.kit) : Open request R := by
  intro i H fit j K
  obtain ⟨pos, one, cap, delay, cash⟩ :=
    WilsonOriginalSmallStrip.on_run (calendar request) R purchase i H fit
  refine ⟨_, pos, one, delay, ?_⟩
  intro n hn
  have member : n ∈ range (j+1) := mem_range_succ_iff.mpr hn
  have before := (Finset.le_sup (f := fun k => (request k).threshold K j) member).trans (purchase.1 j)
  let t : Fin (j+1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have narrow := Finset.inf'_le (f := fun k : Fin (j+1) => (request k.val).cap K j H) (Finset.mem_univ t)
  have after := (le_abs_self ((request n).bill K j H)).trans
    (Finset.single_le_sum (f := fun k => |(request k).bill K j H|) (fun _ _ => abs_nonneg _) member)
  refine ⟨?_, cap.trans narrow, after.trans cash⟩
  simpa only [R.alloy.B.valid.lengths] using before

/-- A single positive strip also works across all the active horizons of the date. -/
theorem all_horizons (request : ℕ → Menu G) (R : Run G) (paid : Open request R) (i : ℕ) :
    let j := R.alloy.B.a.clock.J i
    let K := R.metals.p.kernel
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ Real.exp (σ⁻¹^2) ≤ R.alloy.B.a.clock.hatBeta i ∧
      ∀ H, H ≤ j → ∀ n, n ≤ j → (request n).threshold K j ≤ (R.rolls.L j).val ∧
        σ ≤ (request n).cap K j H ∧ (request n).bill K j H ≤ budgetR R i := by
  intro j K
  have clearing (h : Fin (j+1)) := paid i h.val (Nat.le_of_lt_succ h.isLt)
  choose width wage using clearing
  obtain ⟨h, _, smallest⟩ := Finset.exists_min_image Finset.univ width Finset.univ_nonempty
  refine ⟨width h, (wage h).1, (wage h).2.1, (wage h).2.2.1, ?_⟩
  intro H hH n hn
  let k : Fin (j+1) := ⟨H, Nat.lt_succ_of_le hH⟩
  obtain ⟨floor, cap, fare⟩ := (wage k).2.2.2 n hn
  exact ⟨floor, (smallest k (Finset.mem_univ k)).trans cap, fare⟩

/-- The same capped roots, books and forecast give the actual period-uniform
lesson and Wilson history. -/
def Capped (simple : G.Simple) (law : VowsR.LawScroll G φ) (R : Run G) : Prop :=
  let menu := WilsonOlderFreshGraphAllStages.menu G
  let D := WilsonOlderFreshGraphSchool.roots menu simple R.metals.p R.metals.K
  let Q := WilsonOlderFreshGraphSchool.rollTab menu simple R.metals R.rolls
  ∃ books : Offices.Books D R.rolls Q φ, ∃ F : Forecast D R.rolls Q φ books,
    Treehouse.VariableHouse R D Q law books R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) ∧
    Oak.Semester R D Q books F

theorem semester (R : Run G) (simple : G.Simple) (law : VowsR.LawScroll G φ)
    (split : MintClock.splits ≤ φ) (U : ℕ → ℕ)
    (stock : WilsonOlderFreshGraphCommonHouse.supply simple law split U R.kit) :
    Capped simple law R := by
  let menu := WilsonOlderFreshGraphAllStages.menu G
  let D := WilsonOlderFreshGraphSchool.roots menu simple R.metals.p R.metals.K
  let Q := WilsonOlderFreshGraphSchool.rollTab menu simple R.metals R.rolls
  obtain ⟨⟨books, chamber⟩, _⟩ := WilsonOlderFreshGraphAllStages.original simple R
    (WilsonOlderFreshGraphCommonHouse.course law split) stock.1
  obtain ⟨F, house⟩ := WilsonWindowUniversalSchool.house simple R D Q law books split chamber stock.2
  exact ⟨books, F, house, house.licence.plan⟩

theorem original (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap)
    (simple : G.Simple) {ε ξ : ℝ} (positive : 0 < ε) (finance : Glacier (a := a) simple ξ)
    (law : VowsR.LawScroll G φ) (split : MintClock.splits ≤ φ)
    (permitted : ∀ (s : Sheet G) (q : MapPrices), Permitted law s (ThroughLaunch.raging s q))
    (request : ℕ → Menu G) (bills : ℕ → ℕ → Gear G → ℝ) (extra : Prediction G)
    (paid : WilsonFundedWindowMenu.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      OnRun.{u} cap simple ε law U (@demands G φ simple law split U bills
        (Together (@WilsonOriginalSmallStrip.Filed G (calendar request)) (@extra))) R T W ∧
      Capped simple law R ∧ Open request R ∧ WilsonPositionProgramNestedElection.course simple a ξ R.kit ∧
      R2I.RG05Joint.AcrossPanels R.kit ∧ (∀ i, (R.family.path.levels.budget i).supportExponent = 100) ∧
      Quiet R ∧ ∀ cohort : Ultrafilter (ℕ × ℕ) → Prop,
        (∀ (f : Extraction.Order) (l : Ultrafilter (ℕ × ℕ)), (l : Filter (ℕ × ℕ)) ≤ f.fuse → cohort l) →
        WilsonMacroscopicFundedReader.Elected.{u} R simple cohort := by
  let supplement := @Together G (@WilsonOriginalSmallStrip.Filed G (calendar request)) (@extra)
  have grant : WilsonFundedWindowMenu.AllPrices (@supplement) := fun s q =>
    joint (WilsonOriginalSmallStrip.prepaid simple (calendar request) s _) (paid s q)
  obtain ⟨R, T, W, school, nested, panels, support, quiet, physical⟩ :=
    WilsonOriginalSeparatedElection.original.{u} a cap U mono simple positive finance law split permitted
      bills (@supplement) grant
  exact ⟨R, T, W, school, semester R simple law split U school.2.1.1,
    opened request R school.2.1.2.2.2.1, nested, panels, support, quiet, physical⟩

/-- The original physical-history scroll is permitted for every sheet. -/
abbrev physical (a : Axis) (cap U : ℕ → ℕ) (mono : Monotone cap)
    (simple : G.Simple) {ε ξ : ℝ} (positive : 0 < ε) (finance : Glacier (a := a) simple ξ)
    (request : ℕ → Menu G) (bills : ℕ → ℕ → Gear G → ℝ) :=
  original.{u} a cap U mono simple positive finance
    (WilsonPhysicalHistoryPriorAperture.law G MintClock.splits) le_rfl
    (fun s _ => WilsonPhysicalHistoryPriorSelection.permitted MintClock.splits s _)
    request bills (@WilsonReportColumnSubsidy.Eligible G) WilsonReportColumnSubsidy.allPrices

end YM.Integration.WilsonOriginalSeparatedCalendar
end

