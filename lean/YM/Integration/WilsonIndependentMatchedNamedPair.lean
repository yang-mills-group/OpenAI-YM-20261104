import YM.Integration.WilsonIndependentMatchedClosedPlan
import YM.Integration.WilsonOriginalPivotWardSurvey
import YM.Integration.WilsonOriginalPublicPlantedLetters

/-! The finite product in the actual measured and conventional section charts
is a joint shifted Wilson integral on the same conventional tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedNamedPair
open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace
open FVA2 PhysicalNext.Repeat.Legato SlotEvaluation XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Binding
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (W:Initialize G) (Y:Sample 2)
local notation "T" => W.tree Y.F.p
local notation "F" d:max => R.family.labels.level d

def sectionAt (survey:Bool) (d:ℕ): SectionData (F d) :=
  if survey then WilsonOriginalPivotWardSurvey.sectionAt R W d else R.family.localSection d

def placed (survey:Bool) (d:ℕ) (o:Cover) (b:(F d).Index) :=
  fieldAt (sectionAt R W survey d) b (wrap Y.F.p.side o)

def printed (survey:Bool) (d:ℕ) (o:Cover) (b:(F d).Index) : Bare.Series T G :=
  if survey then Bare.raw T (W.surveys d) (wrap Y.F.p.side o) ((F d).basis b).val
  else WilsonOriginalPublicPlantedLetters.letter R Y.F.p T d o b

theorem admitted (survey:Bool) (d:ℕ) (o:Cover) (b:(F d).Index):
    Orb.PreTest (placed R W Y survey d o b) := by
  cases survey with
  | true =>
    have h:=WilsonOriginalPivotWardSurvey.issued R W d
    exact (pre_field _ h.1 h.2.1 b _).1
  | false => exact (pre_field _ (R.makes.sections d) (FVAAlt2.Block.clothes R d) b _).1

theorem ranked (survey:Bool) (d:ℕ) (o:Cover) (b:(F d).Index):
    PowerSeries.X^((F d).grades b).2 * printed R W Y survey d o b =
      BareOrb.stencil T (placed R W Y survey d o b) := by
  cases survey with
  | true => simpa [printed,placed,sectionAt,Bare.scalar] using
      WilsonOriginalPivotWardSurvey.sampled R W Y d b (wrap Y.F.p.side o)
  | false =>
    change PowerSeries.X^_ * WilsonOriginalPublicPlantedLetters.letter _ _ _ _ _ _ = _
    rw [WilsonOriginalPublicPlantedLetters.shifted]
    unfold BareOrb.stencil TreeFormal.enter
    apply congrArg (Taylor.expandTaylor ((W.tree Y.F.p).basis G))
    funext u
    exact (scalar_real (R.makes.sections d) (i:=b) (o:=wrap Y.F.p.side o) (u:=(W.tree Y.F.p).links u)).symm

theorem pair (a c:Bool) (d e:ℕ)(o z:Cover)(b:(F d).Index)(b':(F e).Index)(q:ℕ):
    coeff q (Bare.normalized T G (printed R W Y a d o b * printed R W Y c e z b')) =
      (plotPT WilsonIndependentMatchedOrbitReading.originalClock
        (WilsonIndependentMatchedOrbitReading.insert
          (placed R W Y a d o b * placed R W Y c e z b'))
        (((F d).grades b).2+((F e).grades b').2) q:ℂ) :=
  WilsonIndependentMatchedClosedPlan.pair T (admitted R W Y a d o b)
    (admitted R W Y c e z b') (ranked R W Y a d o b) (ranked R W Y c e z b')

end YM.Integration.WilsonIndependentMatchedNamedPair

