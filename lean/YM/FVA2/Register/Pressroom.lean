import YM.FVA2.Register.Parameter
import YM.FVA2.Speed.Distill
import YM.FVA2.Feyn.Folio
/-!
# WilsonPrescription: sharing formal-to-formal comparison data

Use `WilsonPrescription` for the algebraic predictions. `prepared` chooses the data;
generating them doesn't require MS data or even the conversion. See `YM/FVA2/Handoff.lean`
for many formulas using them in Wilson-only calculations. This assembly includes the
`XSpace.Initialize`, extra diagnostic tests/solver (including `G.Simple`-enabled
existence via `Rose` etc.), and clock convention for the multiscale eliminations; the $B^a_h$ inputs
are built with those same `Initialize` data via `Arrival/Born.lean`.

There's an intermediate theorem `end_to_continuum` below. See `YM/FVA2/Main.lean` for
the main theorem, using this same prescription, with all the features of the comparison,
including OPE coefficient extraction. These results aren't proofs of analytic estimates on
the actual theory or of a trajectory comparison to a cover hierarchy. Coarsening is on this
same inversion regulator. No requiring here that a particular `StepData` be used, or bounds
on stepwise locality. Theorems don't imply the analytic estimates of the manuscript.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Register
open Function Set Filter Finset MeasureTheory Metric Lattice Wilson
open YM.FVA2 Recall Recall.Move
open MS MS.Plane MS.Koszul MS.Book MS.Book.Convolve Program MS.Native MS.Theater MS.Menus MS.Local.Physical MS.Land
open MS.Orbit MS.Fleet MS.Tide MS.Swirl MS.Swirl.Near MS.Rake Press XPos Change Slice
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking BlockGauge BlockGauge.Fabric OpenSlots.Quadratic
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Orb Facade Hearth RGComparison.Core16
open Arrival Arrival.Episodic XSpace Normalize
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}

-- constrain physical regulators even in the *intermediate* charted descriptions. Don't
-- encode the regulator from e.g. compactness.
def epochUses (R : Run) {n : Side} (p : Fabric G n) : Prop :=
    match p with
    | .endcap _ _ => n=R.finalSide.side
    | .layer S _ _ _ L => R.ratio = S.patch.L.val ∧ epochUses R L
lemma deployment (Q : RG.Patch) (A : Hearth.Asteroid G) (R : Run)
        (h : Q.L.val = R.ratio) (i : ℕ) :
        epochUses R (Hearth.habit G R Q h A i) := by
    induction i with
    | zero => refine PNat.eq ?_; simp [vein, Run.den]
    | succ i ih => exact ⟨ h.symm, ih ⟩
lemma everySide {n : Side} (R : Run) (p : Fabric G n) (h : epochUses R p) : 4 ≤ n.val := by
    cases p with
    | endcap => rw [show n=R.finalSide.side from h]; exact R.finalSide.large
    | @layer c f S H t hf L =>
        have he : R.ratio = S.patch.L.val ∧ epochUses R L := h
        have ht := everySide R L he.2
        refine ht.trans ?_; rw [ S.sizes ]
        exact Nat.le_mul_of_pos_right _ S.patch.L.pos
termination_by structural p

/-- Shared diagram prescription for a simple gauge group. The conventions
fixed by the prescription apply across fields. `Main.Match` supplies the
budget and implementation results, including the detectors and `Steady` data. -/
structure WilsonPrescription (G : Gauge) where
    /-- Includes the stencil data; see the `Survey`s there. -/
    scheme : XSpace.Initialize G
    /-- Nested position normalization. -/
    store : XSpace.Normalize.Store G
    /-- Detect the position coupling by a selected triangle. -/
    criterion : XSpace.Rose.Pick store
    run : XSpace.Run
    chart : Precision.ChartRatio G
    analyticChart : Precision.LocalRatio chart
    /-- Step sequence including the expansion clock. -/
    chooses (i : ℕ) : Epoch G (run.step i).p.side
    sound (i : ℕ) : epochUses run (chooses i).F

namespace WilsonPrescription
-- Existence, including the full Epoch sequence.
include G in
lemma prepared (s:G.Simple) (R:Run) (Y:Initialize G) (c:ℝ) (hc:0<c) :
        ∃ p:WilsonPrescription G, p.run=R ∧ p.scheme=Y := by
    obtain ⟨V⟩ := equipped s; obtain ⟨K⟩ := Rose.nominate Y s V
    obtain ⟨A,hA⟩:= galaxy G c hc
    let F i := Hearth.habit G R (program R 4 (by decide)) rfl A (lots R i)
    exact ⟨ ⟨Y,V,K,R,tray G,traySpec G,fun i=> ⟨F i,localTruss (F i),exampleGear (F i)⟩,
      fun _=> deployment (program R 4 (by decide)) A R rfl _ ⟩, rfl, rfl ⟩

variable (N:WilsonPrescription G) (M:Land.Prescription (Press.portDeck G)) (h:G.Simple)
variable (T: Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "E"=> WilsonPrescription.chooses N
local notation "Ω"=> WilsonPrescription.analyticChart N
local notation "σ"=> WilsonPrescription.scheme N
-- Expectation of the actual stencil words (including the nonlinear/W pieces) at fixed lattice
-- cutoff, using that very coarsening. No MS variable change yet; see `reportFull` below.
abbrev serial (i:ℕ)(b:List (Birth G)) := Episodic.world σ (E i) Ω b

variable {W:Type}[LinearOrder W]

abbrev reportFull (u : W → MS.Rake.Label (Press.portDeck G))
        (L : Cover) (d : W → Cover) (x : ℝ) (v : Finset W) (i : ℕ) : MS.Book.Convolve.T ℂ :=
    Rescaled.posed (offered M.team x) σ (E i) Ω u M L d x v

-- Extends `Quoted` (incl. cost estimates for the measurements) and here in particular makes
-- explicit (route `supplies` and `markT`) that our evolution and insertions in the multi-step
-- form generate the very same predictions.
structure Posted (T : Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
                 (M : Land.Prescription (Press.portDeck G)) : Prop
        extends Speed.Quoted N.scheme N.criterion T M where
    journey : XSpace.Expense.Stretched atTop N.run.step
    supplies (i : ℕ) (b : List (Birth G)) :
        N.serial i b = Birth.words N.scheme ( N.run.step i ).p.side b
    markT {W : Type} [LinearOrder W] (u : W → Label (Press.portDeck G))
            (L : Cover) (d : W → Cover) (i : ℕ) (v : ℝ) (y : Finset W) :
        PhysicalSum G M.team v (N.run.step i).p.side true y d L
          (ApplyMF (Press.wickInput σ) (Stripped M.team) M u) (N.reportFull M u L d v y i)
-- every such insertion type W
include h
/-- Intermediate supplier, starting with independently fixed Wilson inputs.
 One uses `costo` via `Parameter` & `Recall`, or equivalently `Top` via
 `Arrival.Episodic` and `MS.Dial` prices. `dial` allows choosing path from
 either theorem. Includes scale law and coupling uniqueness proofs from `Scale`.
 Uniform even-regulator & kernel & price estimates from `Speed`. -/
theorem end_to_continuum (d:Bool) :
    ∃ M:Prescription (Press.portDeck G),
      M.team=(Continuum.Continuation.proofStart h (Reg.supplies N.scheme T) d).team ∧
        Posted N T M := by
    obtain ⟨M,hM,H⟩ := Speed.comparisonCP7 N.scheme N.criterion T h d
    exact ⟨ M,hM,H, Expense.Stretched.runs N.run, fun i b=> sum_world _ _ _ _,
      fun {W} x u L d i v y => Rescaled.on_clock _ _ _ _ _ _ _ _ _ ⟩

-- Does not require choosing a particular good schedule even for these assembly results: any Run.
omit h
lemma offer (G:Gauge) (g:G.Simple) (R:Run) (b:Bool) :
    ∃ (N:WilsonPrescription G) (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
        (M:Land.Prescription (Press.portDeck G)),
        N.run=R ∧ M.team=(Continuum.Continuation.proofStart g (Reg.supplies N.scheme T) b).team ∧
        Posted N T M := by
    obtain ⟨N,hN,_⟩ := prepared g R ( Initialize.standard G ) 1 one_pos
    obtain ⟨T⟩ := MS.Land.bookedMS ( Position.OpenAxis.Plot (Press.portDeck G) )
    obtain ⟨M,hM,H⟩ := N.end_to_continuum g T b; exact ⟨ N,T,M,hN,hM,H⟩
end WilsonPrescription
end YM.FVA2.Register
