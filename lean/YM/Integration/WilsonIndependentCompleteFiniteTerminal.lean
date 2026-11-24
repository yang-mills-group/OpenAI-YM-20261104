import YM.Integration.WilsonIndependentFreshFiniteTerminal
import YM.Integration.WilsonIndependentFreshRoster

/-! The full countable captured word is passed to the finite terminal Haar
and Gaussian read at a fixed physical regulator. The same original course
and the same weak stop work for every finite subroster of the word. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonIndependentCompleteFiniteTerminal
open WilsonIndependentCapturedTerminal
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Budget RegulatorIR.Spatial RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle RegulatorIR.Atlas
open RegulatorIR.Epoch RegulatorIR.Calibration RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Binding RegulatorIR.Geometry RegulatorIR.Halo RegulatorIR.FVAAlt2
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages Pert.Asymptotics
open scoped ENNReal Classical Topology
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type}
local notation "program" => Oracle.books C.family.path.levels.clock.kernel

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
      ∃ seed : (S.dialect (program) G branch (sheet F)).Primitive
          (WilsonIndependentCapturedCalendar.meter C D m j w) order (quantum 1 0),
      let L := S.dialect (program) G branch (sheet F)
      let T := b.after.part L (S.payroll (program) G branch (sheet F)) seed
      let M := WilsonIndependentFreshReel.margins (S.lane (program) G branch (sheet F)) b.after
      ∀ (ι : Type) [Nonempty ι] (arity offset : ℕ) (parts : ι → T.Report arity) (total : T.Report arity)
        (film : X → ι → Portrait G), (∀ x a, BasisT arity offset (film x a)
          ((parts a).main (Page.opening b.after.spans x))) →
      ∀ (l : Filter ι) [NeBot l], (∀ x, Tendsto (fun a => (parts a).point (Page.opening b.after.spans x))
          l (𝓝 (total.point (Page.opening b.after.spans x)))) →
      ∀ (root : X → Room), L.cushion (1/8) root → ∀ (gross : X → ℝ), (∀ x, 0 ≤ gross x) →
        (∀ (choose : X → ι) i, i ≤ order → ∀ r, 0 < r →
          Claim (WilsonIndependentCapturedCalendar.meter C D m j w)
            (fun x => L.coverQ root 2 (b.choose x)) (fun x => ENNReal.ofReal (gross x))
            (fun x => (parts (choose x)).main (Page.opening b.after.spans x) i r)) →
      ∀ e, e ≤ order → ∀ᶠ t : ℕ in atTop, ∀ x, report x=t →
        ∀ N per : ℕ, B.reporter+t ≤ N →
        let g := regulatorRun C.family N per (B.reporter+t)
        gross x ≤ (g^debt)⁻¹ →
        ‖(b.after.expanse L).vista T total M x e -
          note (total.point ((WilsonIndependentFreshScalar.remaining b last).choose x) e 0)‖ ≤ g^P := by
  classical
  obtain ⟨first,ready⟩ := WilsonIndependentFreshFiniteTerminal.original (X:=X) C D elected paid slow branch order u P debt
  refine ⟨first,?_⟩
  intro stage late B
  obtain ⟨v,scheduled⟩ := ready stage late B
  refine ⟨v,?_⟩
  intro report m j w S b last color F notebook
  obtain ⟨seed,received⟩ := scheduled report color F notebook
  refine ⟨seed,?_⟩
  intro L T M ι hι arity offset parts total film lawful l hl entrance root inside gross nonneg wage e he
  let stop := WilsonIndependentFreshScalar.remaining b last
  let later (x : X) (a : ι) : Prop := ∀ N per : ℕ, B.reporter+report x ≤ N →
    let g := regulatorRun C.family N per (B.reporter+report x)
    gross x ≤ (g^debt)⁻¹ →
      ‖(b.after.expanse L).vista T (parts a) M x e -
        note ((parts a).point (stop.choose x) e 0)‖ ≤ g^P
  have allPaid := WilsonIndependentFreshRoster.uniform report (l:=atTop) later (by
    intro choose
    let bank := WilsonIndependentFreshRoster.assemble (fun x => parts (choose x))
    have heard := received arity offset bank (fun x => film x (choose x))
      (fun x => lawful x (choose x)) root inside gross nonneg (wage choose) e he
    filter_upwards [heard] with t ok x site
    subst t
    exact ok x rfl)
  filter_upwards [allPaid] with t paidFace x site N per cut g cap
  subst t
  exact WilsonIndependentOccupiedVista.complete (b.after.expanse L) T parts total l M
    (WilsonIndependentFreshScalar.start b) stop (fun _ => Nat.zero_le _) entrance x e (g^P)
    (Filter.Eventually.of_forall (fun a => paidFace x rfl a N per cut cap))

end YM.Integration.WilsonIndependentCompleteFiniteTerminal
