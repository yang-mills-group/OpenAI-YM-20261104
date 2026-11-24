import YM.Integration.WilsonGraphIncumbentWardSeriesPublication
import YM.Integration.WilsonGraphWardGroundMatrix
import YM.Integration.WilsonGraphAppointedWardGroundMatrix
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroupFirstWardTree
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroupMaxwellIntegrability
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion
import YM.Integration.WilsonGraphAppointedWardGroundRhs
import YM.Integration.WilsonGraphAppointedWardTranslationRow
import YM.Integration.WilsonGraphAppointedWardUnitFlux
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellProfileGradients

set_option autoImplicit false

noncomputable section
universe u

namespace YM.Integration.WilsonGraphIncumbentWardTestedGround

open _root_.YangMills _root_.YangMills.Matching
open _root_.YM.Maxwell _root_.YM.Maxwell.Wick
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils probes)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients (groupMarked fluxEntry rhsCoefficients)
open _root_.PhysicalMatching.H7StandaloneTranslationTestSupport (weight)
open WilsonGraphWardGroundMatrix (Tested reading)
open WilsonGraphPaperPublication (prescription perspective)
open WilsonGraphIncumbentWardSeriesPublication (groupPupils groundMatrix)
open MeasureTheory Filter Set
open scoped BigOperators Classical Topology

variable {g : GaugeGroup}

private def letters (H : g.core.Simple) {n : ℕ} (a : Axis) (t : Fin n → Fin 2) (l : Fin 4) :
    Fin (n + 1) → _root_.YangMills.MSbar.Ordinary.Label (maxwellReference g) :=
  Fin.cons ⟨4, columns H a 0 l⟩ (fun i => ⟨4, probes H (t i)⟩)

def wickWord (H : g.core.Simple) {n : ℕ} (a : Axis) (t : Fin n → Fin 2) (l : Fin 4) :
    Fin (n + 1) → WickPol g.core :=
  fun i => (letters H a t l i).2.val

theorem filedAt (S : Conversion (maxwellReference g)) (H : g.core.Simple) {n : ℕ}
    (a : Axis) (t : Fin n → Fin 2) (l : Fin 4) (x : Points (n + 1))
    (hx : x ∈ separated (n + 1)) :
    reading S (fun i => probes H (t i)) (columns H a 0 l) x =
      _root_.YM.Maxwell.Wick.moment g.core x (wickWord H a t l) :=
  _root_.PhysicalMatching.H7IndependentGroupFirstWardTree.groupLeading S (letters H a t l) x hx

theorem markedAt {H : g.core.Simple} (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
    (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true) {n : ℕ} (a : Axis)
    (t : Fin n → Fin 2) (l : Fin 4) (x : Points (n + 1)) (hx : x ∈ separated (n + 1)) :
    groupMarked Z Q 0 a 0 l t x = _root_.YM.Maxwell.Wick.moment g.core x (wickWord H a t l) :=
  (WilsonGraphAppointedWardGroundMatrix.marked Z Q a l t x hx).trans
    (filedAt _ H a t l x hx)

theorem tested (S : Conversion (maxwellReference g)) (H : g.core.Simple) {n : ℕ}
    (a : Axis) (t : Fin n → Fin 2) {X : Type*} [MeasureSpace X]
    (shape : X → Points (n + 1)) (w : X → ℂ)
    (occupied : ∀ z, w z ≠ 0 → shape z ∈ separated (n + 1))
    (paid : ∀ l, Integrable (fun z => w z *
      _root_.YM.Maxwell.Wick.moment g.core (shape z) (wickWord H a t l))) :
    Tested S H a t shape w := by
  refine ⟨occupied, ?_⟩
  intro l
  apply (paid l).congr
  filter_upwards [] with z
  by_cases hz : w z = 0
  · simp [hz]
  · rw [filedAt S H a t l (shape z) (occupied z hz)]

theorem vacuum (S : Conversion (maxwellReference g)) (H : g.core.Simple) (P : Pupils) :
    Tested S H 0 (fun i : Fin 0 => Fin.elim0 i) id (fun x => P.vacuum x) := by
  apply tested S H 0 (fun i : Fin 0 => Fin.elim0 i) id (fun x => P.vacuum x)
    (fun x hx => P.vacuum.tsupport_subset (subset_tsupport _ hx))
  intro l
  exact _root_.PhysicalMatching.H7IndependentGroupMaxwellIntegrability.testedMomentIntegrable
    (wickWord H 0 (fun i : Fin 0 => Fin.elim0 i) l) P.vacuum

theorem conservation (S : Conversion (maxwellReference g)) (H : g.core.Simple) (P : Pupils)
    (row j : Fin 2) (a : Axis) :
    Tested S H a (fun _ : Fin 1 => j) id
      (fun x => Ward.firstDerivative a (fun y => P.conservation row j y) x) := by
  apply tested S H a (fun _ : Fin 1 => j) id
    (Ward.firstDerivative a (fun y => P.conservation row j y))
    (fun x hx => (_root_.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion.derivativeWeight
      (P.conservation row j) a).2.2 (subset_tsupport _ hx))
  intro l
  exact _root_.PhysicalMatching.H7IndependentGroupMaxwellIntegrability.testedDerivativeMomentIntegrable
    (wickWord H a (fun _ : Fin 1 => j) l) (P.conservation row j)
    (PiLp.single 2 0 (EuclideanSpace.single a 1))

theorem translation (S : Conversion (maxwellReference g)) (H : g.core.Simple) (P : Pupils)
    (a : Axis) : Tested S H a (fun _ : Fin 2 => 0)
      (fun z : Spacetime × Points 2 => Ward.prepend z.1 z.2) (weight P a) := by
  apply tested S H a (fun _ : Fin 2 => 0)
    (fun z : Spacetime × Points 2 => Ward.prepend z.1 z.2) (weight P a)
    (fun z hz => _root_.PhysicalMatching.H7StandaloneTranslationTestSupport.separated P a
      (subset_tsupport _ hz))
  intro l
  exact _root_.PhysicalMatching.H7IndependentGroupMaxwellIntegrability.signedShellMomentIntegrable
    (wickWord H a (fun _ : Fin 2 => 0) l) (weight P a)
    (_root_.PhysicalMatching.H7StandaloneTranslationTestSupport.smoothWeight P a)
    (_root_.PhysicalMatching.H7StandaloneTranslationTestSupport.compact P a)
    (fun _ hz => _root_.PhysicalMatching.H7StandaloneTranslationTestSupport.separated P a hz)

theorem onGroup (g : GaugeGroup) (hg : g.IsSimple) :
    WilsonGraphIncumbentWardSeriesPublication.groundTests g hg := by
  let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  let S := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion
  let P := groupPupils g hg
  exact ⟨vacuum S H P, conservation S H P, translation S H P⟩

theorem fourthRhs (g : GaugeGroup) (hg : g.IsSimple) :
    rhsCoefficients (prescription g hg) (perspective.{u} g hg) (groupPupils g hg) 0 3 = 1 := by
  let H := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  refine (congrFun (WilsonGraphAppointedWardGroundRhs.atPupils
    (prescription g hg) (perspective.{u} g hg) (groupPupils g hg)) 3).trans ?_
  exact _root_.PhysicalMatching.H7IndependentFiledMaxwellProfileGradients.normalizedRhs g H
    (WilsonGraphWardGroundPupils.pricePositive H)

theorem fourthRow (g : GaugeGroup) (hg : g.IsSimple) (j : Fin 4) :
    groundMatrix.{u} g hg 3 j =
      _root_.PhysicalMatching.H7IndependentFourMaxwellWardReadings.leading
        (groundMatrix.{u} g hg 3 1) (groundMatrix.{u} g hg 3 2) 3 j := by
  fin_cases j
  · change fluxEntry (prescription g hg) (perspective.{u} g hg) (groupPupils g hg) 0 0 = 0
    exact WilsonGraphAppointedWardUnitFlux.atPupils
      (prescription g hg) (perspective.{u} g hg) (groupPupils g hg)
  · rfl
  · rfl
  · change fluxEntry (prescription g hg) (perspective.{u} g hg) (groupPupils g hg) 0 3 = 1
    exact (WilsonGraphAppointedWardTranslationRow.atPupils
      (prescription g hg) (perspective.{u} g hg) (groupPupils g hg)).trans (fourthRhs.{u} g hg)

def firstThree (g : GaugeGroup) (hg : g.IsSimple) : Prop :=
  let L := groundMatrix.{u} g hg
  ∀ (i : Fin 3) (j : Fin 4), L i.castSucc j =
    _root_.PhysicalMatching.H7IndependentFourMaxwellWardReadings.leading (L 3 1) (L 3 2) i.castSucc j

theorem publication (first : ∀ (g : GaugeGroup) (hg : g.IsSimple), firstThree.{u} g hg) :
    WilsonGraphStandaloneCorrelation.OnPublication WilsonGraphGroupPositionReference.external
      WilsonGraphPaperPublication.issued.{u} := by
  refine WilsonGraphIncumbentWardSeriesPublication.publication.{u} ?_ onGroup
  intro g hg i j
  exact Fin.lastCases (fourthRow.{u} g hg j) (fun k => first g hg k j) i

end YM.Integration.WilsonGraphIncumbentWardTestedGround
end

