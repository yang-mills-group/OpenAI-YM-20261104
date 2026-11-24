import MSFormalSeries
import MSPositionFrame
import MSScalarReverse

/-! Convert the continuum MS coefficients to the prescribed position scheme at
unit renormalization scale. The field equations are solved before the triangle is read. The
mass-independent position frame keeps the blocks of equal engineering weight
in the reparametrized field series. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.MSbar

open MeasureTheory
open scoped BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}

namespace Position

/-- The three ordinary moments are first combined at a fixed geometry, with a
unit in each omitted slot. Multiplication of power series convolves all lower
orders. The profile is only applied after the connected coefficient is formed. -/
def triangleKernel (M : Coefficients B) (P : PositionPrescription B)
    (k : ℕ) (x : Points 3) : ℂ :=
  let face (I : Finset (Fin 3)) : PowerSeries ℂ :=
    PowerSeries.mk fun j => rawMoment M P 6 j 3 (P.triangle.face I) x
  PowerSeries.coeff k (connectedThree face)

def triangleAmplitude (M : Coefficients B) (P : PositionPrescription B) (k : ℕ) : ℂ :=
  ∫ x, P.triangle.profile x * triangleKernel M P k x

/-- The signed cubic tree calibration fixes the slope. Centering subtracts the
constant term of the measured series before compositional inversion. -/
def measuredCoupling (M : Coefficients B) (P : PositionPrescription B) (k : ℕ) : ℂ :=
  (triangleAmplitude M P k - if k = 0 then triangleAmplitude M P 0 else 0) /
    (P.triangle.cT : ℂ)

def positionReading (M : Coefficients B) (P : PositionPrescription B) (k : ℕ) : ℝ :=
  (measuredCoupling M P k).re

def msCoupling (M : Coefficients B) (P : PositionPrescription B) : ℕ → ℝ :=
  Series.inverseCoupling (positionReading M P)

/-- The raw position field map in the measured coupling. Its unequal-weight
blocks are still present at this stage. -/
def reparametrizedFrame (M : Coefficients B) (P : PositionPrescription B) : Series.Frame B :=
  Series.reparametrize B (msCoupling M P) (rawFrame M P)

/-- Compose scalar formal series with zero constant term, through one chosen
degree. The inverse equations use both orders of composition. -/
def composeAt (outer inner : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), outer j * Matching.couplingPower inner j k

@[simp] theorem positionReading_zero (M : Coefficients B) (P : PositionPrescription B) :
    positionReading M P 0 = 0 := by
  simp [positionReading, measuredCoupling]

/-- Once the independent cubic slope has the prescribed value, direct formal
reversion gives both inverse identities through every order. -/
theorem reversion (M : Coefficients B) (P : PositionPrescription B)
    (slope : positionReading M P 1 = 1) (k : ℕ) :
    composeAt (positionReading M P) (msCoupling M P) k = (if k = 1 then 1 else 0) ∧
    composeAt (msCoupling M P) (positionReading M P) k = (if k = 1 then 1 else 0) :=
  ⟨Series.coupling_after_inverse _ (positionReading_zero M P) slope k,
    Series.inverse_after_coupling _ (positionReading_zero M P) slope k⟩

/-- Multiplying the prescribed correction into the raw field series in the
measured coupling gives exactly its homogeneous, equal-weight part. -/
theorem correction_factorizes (M : Coefficients B) (P : PositionPrescription B) :
    let D := reparametrizedFrame M P
    Series.cauchy B D (Series.adjustment B D) = Series.gradeFrame B D := by
  let D := reparametrizedFrame M P
  have lead (d : ℕ) : D d 0 = LinearMap.id :=
    (Series.reparametrize_zero B (msCoupling M P) (rawFrame M P) d).trans (rawFrame_zero M P d)
  exact funext fun d => funext fun k => Series.cauchy_adjustment B D lead d k

end Position

/-- Formal data used by the physical comparison. The measured fields on the
physical side realize the jets in `adjustment`. -/
structure PositionConversion (B : Maxwell.Reference g) where
  conversion : Matching.Conversion B
  adjustment : Series.Frame B

/-- The conversion equations involve only the public continuum MS arrays, the
free normalization menu, and formal series. Every coefficient of the coupling,
the field map, its inverse and the strictly lowering correction is determined. -/
structure ConversionValid (M : Coefficients B) (P : PositionPrescription B)
    (W : PositionConversion B) : Prop where
  raw : Position.RawValid M P
  integrable (k : ℕ) :
    Integrable (fun x => P.triangle.profile x * Position.triangleKernel M P k x)
  freeOffset : Position.triangleAmplitude M P 0 = 0
  rawSlope : P.triangle.RawSlopeAgrees M
  signedTree : Position.triangleAmplitude M P 1 = (P.triangle.cT : ℂ)
  nonzeroTree : P.triangle.cT ≠ 0
  real (k : ℕ) : (Position.positionReading M P k : ℂ) = Position.measuredCoupling M P k
  slope : Position.positionReading M P 1 = 1
  coupling : W.conversion.f = Position.msCoupling M P
  inverseReading (k : ℕ) :
    Position.composeAt (Position.positionReading M P) W.conversion.f k =
      (if k = 1 then 1 else 0) ∧
    Position.composeAt W.conversion.f (Position.positionReading M P) k =
      (if k = 1 then 1 else 0)
  fields : W.conversion.Z = Series.gradeFrame B (Position.reparametrizedFrame M P)
  inverseFields : W.conversion.Zinv =
    Series.inverseFrame B (Series.gradeFrame B (Position.reparametrizedFrame M P))
  correction : W.adjustment = Series.adjustment B (Position.reparametrizedFrame M P)
  factorization : Series.cauchy B (Position.reparametrizedFrame M P) W.adjustment =
    W.conversion.Z
  startsAtIdentity (d : ℕ) : W.adjustment d 0 = LinearMap.id
  strictlyLowering (d h k : ℕ) (p : B.sector d) (hp : Matching.Homogeneous B h p.val) :
    ∀ m ∈ (W.adjustment d (k + 1) p).val.support,
      Finsupp.weight (fun i : B.toCoordinates.Key => i.1 + 2) m < h

/-- Uniqueness uses exact equality of the four series. In particular it does
not depend on uniqueness of a Wilson hierarchy or of a physical fit. -/
theorem conversionValid_unique {M : Coefficients B} {P : PositionPrescription B}
    {A C : PositionConversion B} (hA : ConversionValid M P A) (hC : ConversionValid M P C) :
    A = C := by
  have sameFields (U V : Matching.Conversion B) (f : U.f = V.f)
      (z : U.Z = V.Z) (i : U.Zinv = V.Zinv) : U = V := by
    cases U
    cases V
    dsimp at f z i
    subst_vars
    rfl
  have eqConversion : A.conversion = C.conversion := sameFields _ _
    (hA.coupling.trans hC.coupling.symm)
    (hA.fields.trans hC.fields.symm)
    (hA.inverseFields.trans hC.inverseFields.symm)
  have eqCorrection := hA.correction.trans hC.correction.symm
  cases A
  cases C
  dsimp at eqConversion eqCorrection
  subst_vars
  rfl

end YangMills.MSbar
