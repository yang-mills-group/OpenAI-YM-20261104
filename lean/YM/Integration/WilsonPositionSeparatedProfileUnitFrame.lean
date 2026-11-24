import YM.Integration.WilsonPositionHomogeneousFrame

/-! The original two running changes preserve the physical unit at each engineering horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileUnitFrame

open Function Filter Set Lattice Wilson RG Source Extraction Table Spec OPE Orbits Climb RG17 Trace.Pilot
  PhysMS Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register PhysicalNext.Repeat.Legato
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)

theorem free (d : ℕ) :
    (Maxwell.Free.fields R.family.labels d).symm (leaf G d)=(Bel R.family.book).unit d := by
  apply Maxwell.Free.address_inj R.family.labels d
  rw [Maxwell.Free.address_eval,LinearEquiv.apply_symm_apply,Maxwell.Free.unit_address]
  rfl

theorem funded (lead : Leading F J) (d : ℕ) : ∀ᶠr in trail,
    WilsonPositionHomogeneousFrame.homogeneous F J Z r d
      ((Maxwell.Free.fields R.family.labels d).symm (leaf G d))=S.unit d := by
  let E:=Maxwell.Free.fields R.family.labels d
  have following (r : ℝ) :
      WilsonPositionHomogeneousFrame.change F J Z d r (E.symm (leaf G d))=E.symm (leaf G d) := by
    unfold WilsonPositionHomogeneousFrame.change
    split_ifs with h
    · simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply,
        E,solitary]
    · rfl
  have first (r : ℝ) :
      WilsonPositionPrescribedFrame.change F J Z.store d r (E.symm (leaf G d))=E.symm (leaf G d) := by
    unfold WilsonPositionPrescribedFrame.change
    split_ifs with h
    · simp only [LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply,
        E,solitary]
    · rfl
  filter_upwards [lead.unit d] with r unit
  change J r d (WilsonPositionPrescribedFrame.change F J Z.store d r
      (WilsonPositionHomogeneousFrame.change F J Z d r (E.symm (leaf G d))))=_
  rw [following,first,WilsonPositionSeparatedProfileUnitFrame.free,unit]

end YM.Integration.WilsonPositionSeparatedProfileUnitFrame
