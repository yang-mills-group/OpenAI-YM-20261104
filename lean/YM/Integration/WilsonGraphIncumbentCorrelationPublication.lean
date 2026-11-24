import YM.Integration.WilsonGraphIncumbentWardTestedGround
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion
import YM.Integration.WilsonGraphIncumbentWardSeriesPublication
import YM.Integration.WilsonGraphPublishedReturnLaws

set_option autoImplicit false

noncomputable section
universe u

namespace YM.Integration.WilsonGraphIncumbentCorrelationPublication

open _root_.YangMills _root_.YangMills.Matching
open _root_.YM.Maxwell _root_.YM.Maxwell.Wick
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils probes)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
  (groupMarked vacuumEntry conservationEntry)
open WilsonGraphIncumbentWardTestedGround (wickWord markedAt firstThree)
open WilsonGraphIncumbentWardSeriesPublication (groupPupils groundMatrix series)
open WilsonGraphPaperPublication (prescription perspective)
open WilsonGraphPublishedReturnLaws (measurementOnPick)
open MeasureTheory Filter Set
open scoped BigOperators Classical

variable {g : GaugeGroup}

theorem singletonWord (H : g.core.Simple) (k : Fin 4) :
    wickWord H 0 (fun i : Fin 0 => Fin.elim0 i) k =
      (fun _ : Fin 1 => (columns H 0 0 k).val) := by
  funext i
  fin_cases i
  rfl

theorem pairWord (H : g.core.Simple) (a : Axis) (j : Fin 2) (k : Fin 4) :
    wickWord H a (fun _ : Fin 1 => j) k = ![(columns H a 0 k).val, (probes H j).val] := by
  funext i
  fin_cases i <;> rfl

theorem vacuumOnFiled {H : g.core.Simple} (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
    (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true) (P : Pupils) (k : Fin 4) :
    vacuumEntry Z Q P 0 k =
      ∫ x : Points 1, P.vacuum x * moment g.core x (fun _ => (columns H 0 0 k).val) := by
  unfold vacuumEntry
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : P.vacuum x = 0
  · simp [hx]
  · rw [markedAt Z Q 0 (fun i : Fin 0 => Fin.elim0 i) k x
      (P.vacuum.tsupport_subset (subset_tsupport _ hx)), singletonWord H k]

theorem conservationOnFiled {H : g.core.Simple}
    (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
    (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true) (P : Pupils) (i : Fin 2) (k : Fin 4) :
    conservationEntry Z Q P 0 i k =
      _root_.PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation.conservation g H P i k := by
  unfold conservationEntry _root_.PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation.conservation
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply integral_congr_ae
  filter_upwards [] with x
  let w := Ward.firstDerivative a (fun y => P.conservation i j y) x
  change w * groupMarked Z Q 0 a 0 k (fun _ : Fin 1 => j) x =
    w * moment g.core x ![(columns H a 0 k).val, (probes H j).val]
  by_cases hz : w = 0
  · simp [hz]
  · have hx : x ∈ separated 2 :=
      (_root_.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion.derivativeWeight
        (P.conservation i j) a).2.2 (subset_tsupport _ hz)
    exact congrArg (fun t : ℂ => w * t)
      ((markedAt Z Q a (fun _ : Fin 1 => j) k x hx).trans
        (congrArg (fun v : Fin 2 → _root_.YM.Maxwell.WickPol g.core => moment g.core x v)
          (pairWord H a j k)))

theorem firstRows (g : GaugeGroup) (hg : g.IsSimple) : firstThree.{u} g hg := by
  let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  let Z := prescription g hg
  let Q := perspective.{u} g hg
  let P := groupPupils g hg
  have one (k : Fin 4) : vacuumEntry Z Q P 0 k = if k = 0 then 1 else 0 :=
    (vacuumOnFiled Z Q P k).trans
      (_root_.PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation.vacuumRow g H
        (WilsonGraphWardGroundPupils.pricePositive H) k)
  have two (i : Fin 2) (k : Fin 4) :
      conservationEntry Z Q P 0 i k = if k = (![1, 2] : Fin 2 → Fin 4) i then -1 else 0 :=
    (conservationOnFiled Z Q P i k).trans
      (_root_.PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation.conservationRows g H
        (WilsonGraphWardGroundPupils.pricePositive H) i k)
  intro i k
  fin_cases i
  · change vacuumEntry Z Q P 0 k = _
    rw [one k]
    fin_cases k <;> rfl
  · change conservationEntry Z Q P 0 0 k = _
    rw [two 0 k]
    fin_cases k <;> rfl
  · change conservationEntry Z Q P 0 1 k = _
    rw [two 1 k]
    fin_cases k <;> rfl

theorem allRows (g : GaugeGroup) (hg : g.IsSimple) :
    WilsonGraphIncumbentWardSeriesPublication.leadingRows.{u} g hg := by
  intro i j
  exact Fin.lastCases (WilsonGraphIncumbentWardTestedGround.fourthRow.{u} g hg j)
    (fun k => firstRows.{u} g hg k j) i

theorem onEveryPeriod (g : GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p) :
    WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion (series.{u} g hg) ∧
      CorrelationOnly.namedStress (measurementOnPick.{u} g hg p hp) (series.{u} g hg) :=
  WilsonGraphIncumbentWardSeriesPublication.wardOnPick.{u} g hg (allRows.{u} g hg) p hp

theorem groupSeries (g : GaugeGroup) (hg : g.IsSimple) :
    ∃! P : WardStress.Series (maxwellReference g),
      WardStress.Determined (_root_.IssuedMaxwell.GraphCoefficients.issued g)
        (WilsonGraphGroupPositionReference.external g hg).conversion.conversion P := by
  have paid := (onEveryPeriod.{0} g hg (fun i : ℕ => i) (fun _ _ h => h)).1
  refine ⟨series.{0} g hg, paid, ?_⟩
  intro P hP
  exact WilsonGraphIncumbentWardSeriesPublication.groupUnique.{0} g hg (allRows.{0} g hg)
    (WilsonGraphIncumbentWardTestedGround.onGroup g hg) hP paid

theorem publication :
    WilsonGraphStandaloneCorrelation.OnPublication WilsonGraphGroupPositionReference.external
      (WilsonGraphPaperPublication.issued.{u}) :=
  WilsonGraphIncumbentWardTestedGround.publication.{u} firstRows.{u}

end YM.Integration.WilsonGraphIncumbentCorrelationPublication
end

