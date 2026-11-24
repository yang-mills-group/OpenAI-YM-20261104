import YM.Integration.WilsonPositionSeparatedProfileUnitJet

/-! The heard physical unit is the original conditional Wilson density evaluated on flat links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileFlatField
open Function Set Filter MeasureTheory Labels Lattice Wilson RG Source Analysis Next.Foundations
open ProjectorNext.Equivariance Trace.Physical Push.Local RG05Readout Address Native
open MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open PhysicalNext.Repeat.Legato Bandage Harvest Velvet Pulse Many
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {n : Side}

theorem vacuum {F : Labels.Frame G 0} {A : Hol G} (B : SectionData F) (sound : B.Sound A)
    (R : RG.Rep G n) (o : Site n) (q : Coefficient F n) (format : q.Format o A R) :
    q.density o B R 1 = (R.eval 1 : ℂ) * q.x 0 := by
  have flags : RG.flags R.p.threshold (1 : Config G n) = ∅ := (offFlags _ R.p.threshold_pos).self_of_nhds
  rw [noFlagCharge q o B sound flags]
  simp_rw [format.identity_null]
  rw [tsum_zero,add_zero]
  apply congrArg ((R.eval 1:ℂ) * ·)
  have at_one := congrArg (fun a => B.places (F.scaled R.p.threshold⁻¹ a) o (1:Config G n)) (power_zero q.x)
  rw [map_smul,Frame.scaled_unit] at at_one
  rw [at_one]
  simp only [SectionData.places,B.eval_linear.map_smul,sound.unit,Pi.smul_apply,smul_eq_mul,Pi.one_apply,mul_one]

theorem read {C : Family G} (law : C.Makes) {R : RG.Rep G n} {o : Site n} {κ bill : ℝ}
    {tape : Tape G n} {raw M : Palette C 0} (print : Printed C 0 R o κ tape raw M bill) :
    pulseOut tape (Native.line Suede.pip) (1 : Config G n) =
      (R.eval 1 : ℂ) * val M (Suede.mother C) := by
  have equal := WilsonPositionSeparatedProfileUnitJet.identical print
  rw [equal]
  cases print with
  | bind low tail necklace format bounded actual label jet price =>
    rw [←actual]
    change ((together C R o 0 low+tail) (Native.line Suede.pip)).1 1 = _
    rw [together_line low tail necklace Suede.pip,label]
    exact vacuum (C.localSection 0) (law.sections 0) R o (low Suede.pip) (format Suede.pip)

end YM.Integration.WilsonPositionSeparatedProfileFlatField
