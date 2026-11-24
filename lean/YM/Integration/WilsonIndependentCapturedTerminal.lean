import YM.Integration.WilsonIndependentCapturedPages

/-! The scalar of the full captured prescribed Wilson program at the
original weak stop. The reporter index may be shared by arbitrarily
many cutoffs, periods, sites and finite truncations of a rooted source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedTerminal
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages Pert.Asymptotics
open scoped ENNReal Classical Topology
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type}
local notation "program" => Oracle.books C.family.path.levels.clock.kernel

def birth {stage u d : ℕ} {B : Band C D stage} (v : Stop C D B u d) (report : X → ℕ) :
    Choice (B.span ∘ report) :=
  atDate (m:=B.lower ∘ report) (fun x => B.reporter+report x)
    (fun x => (v.lower (report x)).trans (v.upper (report x)))

def stopped {stage u d : ℕ} {B : Band C D stage} (v : Stop C D B u d) (report : X → ℕ) :
    Choice (B.span ∘ report) :=
  atDate (m:=B.lower ∘ report) (v.date ∘ report) (fun x => v.lower (report x))

/-- The stop is chosen on the original schedule before all its regulators.
The estimate is uniform over a complete indexed family of actual
prescribed reports. Only positive angular ranks require a rooted wage
on the captured packet. Every degree of its constant travels exactly. -/
theorem original {simple : G.Simple} {axis : Axis} {ε : ℝ}
    (elected : WilsonPositionProgramNestedElection.course simple axis ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit)
    (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ patch : Patch, patch.Branches C.family.path.levels.clock.kernel G)
    (order u P debt : ℕ) :
    ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage,
    ∃ v : Stop C D B u (debt+P+1), ∀ report : X → ℕ,
      let m := B.lower ∘ report
      let j := B.span ∘ report
      let w := B.powers ∘ report
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w (fun x => B.blocks (report x))
      let b := birth C D v report
      let last := stopped C D v report
      ∀ (color : G.ColorIndex) (F : Tent j), Notebook S (program) G branch color (Rocket.native j) F order →
      ∀ (arity offset : ℕ) (Z : (S.payroll (program) G branch (sheet F)).Report arity)
        (portrait : X → Portrait G), (∀ x, BasisT arity offset (portrait x) (Z.main (Page.opening j x))) →
      ∀ (root : X → Room) (gross : X → ℝ), (∀ x, 0 ≤ gross x) →
        (∀ i, i ≤ order → ∀ r, 0 < r → Claim (WilsonIndependentCapturedCalendar.meter C D m j w)
          (fun x => (S.dialect (program) G branch (sheet F)).coverQ root 2 (b.choose x))
          (fun x => ENNReal.ofReal (gross x)) (fun x => Z.main (b.choose x) i r)) →
      ∀ e, e ≤ order → ∀ᶠ t : ℕ in atTop, ∀ x, report x=t →
        ∀ N per : ℕ, B.reporter+t ≤ N →
        let g := regulatorRun C.family N per (B.reporter+t)
        gross x ≤ (g^debt)⁻¹ →
        ‖note (Z.main (Page.finallyW j x) e 0)-note (Z.main (last.choose x) e 0)‖ ≤ g^P := by
  obtain ⟨ir,chronology⟩ := WilsonIndependentCapturedCalendar.original (X:=X) C D elected paid slow branch order
  obtain ⟨cash,refund⟩ := WilsonIndependentCapturedScale.uniform C D simple
  refine ⟨max ir cash,?_⟩
  intro stage hs B
  obtain ⟨v⟩ := WilsonIndependentCapturedPages.original C D simple slow B u (debt+P+1)
  refine ⟨v,?_⟩
  intro report m j w S b last color F book arity offset Z portrait entered root gross hg wage e he
  have late (x : X) : ir ≤ m x := ((le_max_left _ _).trans hs).trans (B.ready _)
  have ordered : b.age ≤ last.age := fun x =>
    Nat.sub_le_sub_left (v.upper (report x)) _
  obtain ⟨K,h,hK,heard⟩ := chronology m j w (fun x => B.blocks (report x)) late
    color F book arity offset Z portrait entered b last root gross hg wage ordered e he
  have tops (x : X) : B.reporter+report x ≤ m x+j x := by
    change _ ≤ B.lower (report x)+B.span (report x)
    rw [B.top]
    exact Nat.le_add_right _ _
  have lengths (x : X) : S.l (b.choose x)/S.l (last.choose x) =
        C.family.S.a (B.reporter+report x)/C.family.S.a (v.date (report x)) :=
    ratio C D w (fun z => B.blocks (report z)) (fun z => B.reporter+report z)
      (v.date ∘ report) (fun z => (v.lower _).trans (v.upper _)) tops
      (fun z => v.lower _) (fun z => (v.upper _).trans (tops z)) x
  have income := refund stage ((le_max_right _ _).trans hs) B hK h P debt
  filter_upwards [income,v.heard] with t fee go x site N per cut g cap
  have base := heard x
  rw [lengths,site] at base
  have item := go.2 N per cut
  apply base.trans
  change K * (WilsonIndependentCapturedCalendar.fare C D B.lower B.span B.powers (report x))^h * _ ≤ _
  rw [site]
  exact fee N per cut (gross x) _ cap
    (div_nonneg (C.family.S.a_pos _).le (C.family.S.a_pos _).le) item.2.2.1

end YM.Integration.WilsonIndependentCapturedTerminal

