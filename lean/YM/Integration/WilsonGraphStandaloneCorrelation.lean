import MSOrdinaryOPE
import YM.Integration.WilsonMSbarCorrelationHeatAllocation
import YM.MS.Graphical.CommonGates
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.FVA2.Teller.Mass

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonGraphStandaloneCorrelation
open YangMills YangMills.Matching
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2
open YM.XSpace YM.XSpace.Normalize
open scoped BigOperators Classical

variable {g : YangMills.GaugeGroup}

abbrev Label (g : YangMills.GaugeGroup) := YangMills.Matching.Label (maxwellReference g)

/-- The common cutoff is computed from this finite list of submitted grades. -/
def cutoff {n : ℕ} (a : Fin n → Label g) : ℕ :=
  Finset.univ.sup (fun i => (a i).1)

theorem within {n : ℕ} (a : Fin n → Label g) (i : Fin n) : (a i).1 ≤ cutoff a :=
  Finset.le_sup (f := fun t => (a t).1) (Finset.mem_univ i)

/-- The public cutoff sector is the original marked sector of the same group. -/
abbrev sector {d : ℕ} (v : (maxwellReference g).sector d) : Sec g.core d := v

/-- Each label enters the common basis through its own sector inclusion. -/
def marks {n h : ℕ} (a : Fin n → Label g) (fits : ∀ i, (a i).1 ≤ h) :
    Fin n → Sec g.core h := fun i => XSpace.Normalize.up (fits i) (sector (a i).2)

theorem inputGrades {n k : ℕ} (S : Conversion (maxwellReference g))
    (a : Fin n → Label g) (ν : Fin n → Fin (k+1)) :
    cutoff (S.inputs a ν) = cutoff a := rfl

theorem inputMarks {n k h : ℕ} (S : Conversion (maxwellReference g))
    (a : Fin n → Label g) (ν : Fin n → Fin (k+1)) (fits : ∀ i, (a i).1 ≤ h) (i : Fin n) :
    marks (S.inputs a ν) fits i =
      XSpace.Normalize.up (fits i) (S.Z (a i).1 (ν i).val (a i).2) := rfl

theorem publicSeparatedIff {n : ℕ} (x : YangMills.Points n) :
    x ∈ YangMills.separated n ↔ x ∈ YM.conf n := Iff.rfl

theorem calibration : YM.FVA2.Teller.logNu 1 =
    (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 :=
  YM.FVA2.Teller.calibration

/-- The physical scale is fixed before any Wilson run or conversion is supplied. -/
def bareAt {n : ℕ} (a : Fin n → Label g) (x : YM.Points n) (k : ℕ) : ℂ :=
  YM.MS.Graphical.separatedGraphSum (YM.FVA2.Teller.logNu 1) g.core (cutoff a) x k (marks a (within a))

theorem identified {n : ℕ} (a : Fin n → Label g) (x : YM.Points n) (hx : x ∈ conf n)
    (k : ℕ) (T : YM.MS.Land.MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core))) :
    bareAt a x k = Dframe.meteor (YM.FVA2.Teller.logNu 1) T (cutoff a) x k (marks a (within a)) := by
  unfold bareAt
  rw [YM.MS.Graphical.identification_screen (YM.FVA2.Teller.logNu 1) T hx]

/-- The public read uses the same Euclidean positions as the nominated evaluator. -/
def bare (g : YangMills.GaugeGroup) : YangMills.MSbar.Ordinary.Correlation (maxwellReference g) :=
  fun _ k a x => bareAt a x k

theorem represented (g : YangMills.GaugeGroup) :
    ∃ M : YangMills.MSbar.Coefficients (maxwellReference g), M.correlation = bare g :=
  ⟨{ correlation := bare g, ope := 0 }, rfl⟩

/-- Coupling and field coefficients remain external to the independently defined bare read. -/
def converted {n : ℕ} (S : Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → Label g) (x : YangMills.Points n) : ℂ :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
    let used := ∑ i, (ν i).val
    if used + j.val ≤ k then
      (couplingPower S.f j.val (k-used) : ℂ) * bare g n j.val (S.inputs a ν) x
    else 0

theorem converted_read (S : Conversion (maxwellReference g)) (M : YangMills.MSbar.Coefficients (maxwellReference g))
    (read : M.correlation = bare g) {n : ℕ} (k : ℕ) (a : Fin n → Label g) (x : YangMills.Points n) :
    S.correlation M k a x = converted S k a x := by
  rw [YangMills.Matching.CorrelationOnly.allocated, read]
  rfl

/-- A group-level position prescription and finite conversion, fixed independently of the runs.
The compatibility equations only inspect the correlation projection of the older public interface. -/
structure External (g : YangMills.GaugeGroup) where
  menu : YangMills.MSbar.PositionPrescription (maxwellReference g)
  admissible : YangMills.MSbar.Admissible menu
  conversion : YangMills.MSbar.PositionConversion (maxwellReference g)
  realization : YangMills.MSbar.NumericalAdjustment (maxwellReference g) conversion.adjustment
  everyBareSlope (M : YangMills.MSbar.Coefficients (maxwellReference g))
    (read : M.correlation = bare g) (t : YangMills.MSbar.Position.Triangle (maxwellReference g)) :
    t.Admissible → t.RawSlopeAgrees M
  valid (M : YangMills.MSbar.Coefficients (maxwellReference g)) (read : M.correlation = bare g) :
    YangMills.MSbar.ConversionValid M menu conversion

/-- Every refinement uses its original hierarchy and the same measured signed clock and frame.
All arities, external phases, shape derivatives, tested expansions and Ward insertions share them. -/
def OnPublication (external : (g : YangMills.GaugeGroup) → g.IsSimple → External g)
    (issued : YangMills.Wilson.Publication) : Prop :=
  ∀ (g : YangMills.GaugeGroup) (hg : g.IsSimple),
    let B := maxwellReference g
    let I := external g hg
    let run := issued.runs g hg
    issued.coordinates g hg = B ∧
    YangMills.WilsonRegularity run.family ∧ YangMills.Wilson.WilsonTrajectory B run.family ∧
    run.originalPointReturns ∧
    ∃ D : YangMills.Wilson.WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
      let choice := run.refine p hp
      let T := choice.hierarchy
      run.family.Converges (p ∘ choice.indices) (fun v => T.correlation none (T.project ∘ v)) ∧
      D.AdjointOn T ∧ YangMills.Wilson.ObservablePhases.Law D T ∧
      ∃ (H : YangMills.Matching.CorrelationOnly.Measurement B T) (X : T.MaxwellScaling B),
        YangMills.MSbar.CorrelationOnly.appointed I.menu I.realization run.family T H ∧
        (∀ M : YangMills.MSbar.Coefficients B, M.correlation = bare g →
          YangMills.Matching.CorrelationOnly.Estimates M I.conversion.conversion H) ∧
        YangMills.FixedFields.Laws B T X ∧ YangMills.AllRadii.Laws B T X H.frame ∧
        YangMills.AllRadii.FrameBounds B T X H.frame

end YM.Integration.WilsonGraphStandaloneCorrelation
end

