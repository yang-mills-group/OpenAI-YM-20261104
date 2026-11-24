import YM.Integration.ActualRunQlocalNativeTuple
import YM.RG05Readout.Suede.Silver

/-! A concrete same-level native Datum for point evaluation. The exact
order-zero basis scalar is retained and cancelled; no normalized basis
or arbitrary palette bound is assumed. The original root is unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQPointDatum
open Function Lattice Wilson RG Source
open PhysicalNext.Repeat.Legato Extra.Histories
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Flatten
open ComparisonDensity.Address
open scoped Classical ContDiff

def phase : ℂ := (Native.line Suede.pip).val 0

private theorem readout_point (U : Orbit) (f : U.Mood) :
    phase * NativeCalibrationMoodReadout.readout U Suede.pip
      (show depth Suede.pip ≤ U.D from Nat.zero_le _) 0 1 f = f.val 0 := by
  let B : Body := ⟨fun _ => f.val 0, by
    change ContDiff ℝ ∞ (fun _ : E4 => f.val 0)
    exact contDiff_const⟩
  have he :
      NativeCalibrationMoodReadout.readout U Suede.pip
        (show depth Suede.pip ≤ U.D from Nat.zero_le _) 0 1 f =
      readJ Suede.pip 0 B := by
    change (1 : ℂ) •
      (writeC 0 ⟨Tensor.coeff
        (f.val ∘ ActualRunCalibrationTests.coordinates.symm) 0 0, _⟩)
        Suede.pip.2 =
      (writeC 0 (records 0 0 B)) Suede.pip.2
    rw [one_smul]
    apply congrArg (fun T : Native.Orb 0 => (writeC 0 T) Suede.pip.2)
    apply Subtype.ext
    change Tensor.coeff (f.val ∘ ActualRunCalibrationTests.coordinates.symm) 0 0 =
      Tensor.coeff B.val 0 0
    ext v
    simp [Tensor.coeff, B, Function.comp_apply]
  rw [he, mul_comm]
  exact Suede.prompt B

variable {G : Gauge} (R : Run G) {V : Type}
    (p L : ℕ) (o : V → Site (R.family.side L p))
    (order weight : V → ℕ)

/-- Fixed before the fee clock or source coefficients: no level ratio,
higher derivative, orientation or free palette coefficient remains. -/
def datum : ActualRunQlocalNativeTuple.Datum R p L L le_rfl V where
  degree _ := 0
  origin := o
  motion _ := (1, false)
  palette _ := phase • Suede.firstC R.family
  choice _ := (0, Suede.mother R.family)
  order := order
  weight := weight
  depth_le i := Nat.zero_le (order i)

theorem depth_zero (i : V) :
    depth ((datum R p L o order weight).choice i).2.1 = 0 := rfl

theorem constant_eq (i : V) :
    ActualRunQlocalNativeTuple.constant (datum R p L o order weight) i = phase := by
  change ratioX (R.family.S.toDepth (show L ≤ L from le_rfl) p) 0 *
    (phase * val (Suede.firstC R.family) (Suede.mother R.family)) = phase
  rw [Suede.val_first]
  simp [ratioX, ratio_one (R.family.S.toDepth (show L ≤ L from le_rfl) p)]

/-- The auxiliary native atom's actual lattice root is the prescribed root. -/
theorem root_eq (i : V) :
    ActualRunQlocalNativeTuple.root (datum R p L o order weight) i = o i := by
  let r := R.family.S.toDepth (show L ≤ L from le_rfl) p
  have hz : r.embed 0 = 0 := r.root.map_zero
  change affine (1 : Signed) (r.embed (o i)) (r.assemble (0, 0)) = o i
  have hlift : lift (0 : Site r.count) = 0 := by funext; simp [lift]
  rw [Ratio.assemble, hz, hlift]
  simp only [map_zero, zero_add, affine, Signed.act_zero]
  simp only [Ratio.embed, ratio_one r, one_nsmul, wrap_lift]

/-- Full finite-smooth test equality, before any restriction to Body tests. -/
theorem reader_eq (i : V)
    (f : (ActualRunQlocalNativeTuple.orbit (datum R p L o order weight) i).Mood) :
    ActualRunQlocalNativeTuple.reader (datum R p L o order weight) i f = f.val 0 := by
  change QlocalSignedReadout.native (QlocalNativeTests.orbit (order i) (weight i))
    (1, false) (ActualRunQlocalNativeTuple.constant (datum R p L o order weight) i)
    Suede.pip (show depth Suede.pip ≤ order i from Nat.zero_le _)
    (placeR (R.family.S.toDepth (show L ≤ L from le_rfl) p) 0)
    ((((R.family.S.toDepth (show L ≤ L from le_rfl) p).count.val : ℝ))⁻¹) f = f.val 0
  rw [constant_eq, originR, ratio_one (R.family.S.toDepth (show L ≤ L from le_rfl) p)]
  simp only [Nat.cast_one, inv_one]
  change phase * NativeCalibrationMoodReadout.readout
    (QlocalNativeTests.orbit (order i) (weight i)) Suede.pip
    (show depth Suede.pip ≤ order i from Nat.zero_le _) 0 1 f = f.val 0
  exact readout_point _ f

end YM.Integration.ActualOriginalQPointDatum
end
