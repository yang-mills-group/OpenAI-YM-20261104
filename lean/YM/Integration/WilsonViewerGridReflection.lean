import YM.Integration.WilsonViewerAlignedPublic

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonViewerGridReflection
open Function Filter Set MeasureTheory Spec Extraction Table PhysicalNext.Repeat.Legato Lattice
open OPE OPE.Orbits OPE.Orbits.Reader Climb RG17 PhysMS Trace.Pilot
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonViewerElectedHierarchy WilsonPositionHomogeneousFrame
open scoped Classical Topology

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)

def reflect (d:ℕ)(a:Axis) :=
  (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) d a

theorem free (d:ℕ)(a:Axis)(v:RG17.Free R.family d) :
    Maxwell.Free.fields R.family.labels d (reflect (R:=R) d a v)=
      ori (Signed.mirror a).ortho d (reel d (Maxwell.Free.fields R.family.labels d v)) := by
  apply Subtype.ext
  change Maxwell.Free.address R.family.labels d ((Bel R.family.book).mirror (Maxwell.Free.spin_free R.family.labels) d (Signed.mirror a)
    ((Bel R.family.book).conj (Maxwell.Free.spin_free R.family.labels) d v))=_
  rw [Maxwell.Free.address_motion,Maxwell.Free.address_star]
  rfl

private def transformed {d:ℕ}(A:Change G d) : RG17.Free R.family d ≃ₗ[ℂ] RG17.Free R.family d :=
  if h:Bijective (stand A) then
    (Maxwell.Free.fields R.family.labels d).trans
      ((LinearEquiv.ofBijective _ h).trans (Maxwell.Free.fields R.family.labels d).symm)
  else LinearEquiv.refl ..

private theorem respects {d:ℕ}(A:Change G d)(a:Axis)(v:RG17.Free R.family d) :
    transformed (R:=R) A (reflect (R:=R) d a v)=reflect (R:=R) d a (transformed (R:=R) A v) := by
  by_cases h:Bijective (stand A)
  · apply (Maxwell.Free.fields R.family.labels d).injective
    rw [free]
    simp only [transformed,dif_pos h,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
      LinearEquiv.ofBijective_apply,free,stood_reel,stood_ori]
  · simp only [transformed,dif_neg h,LinearEquiv.refl_apply]

variable {course:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {Y:(Bel R.family.book).Hierarchy} {arc:Trace.Terrace.Arch R.family}
    {U:Ultrafilter (ℕ×ℕ)}{simple:G.Simple}{cohort:Ultrafilter (ℕ×ℕ)→Prop}

/-- The reflected pin and the original pin use the same positioned homogeneous public field. -/
theorem original (run:Selected F course Q J Y arc U simple cohort)(d:ℕ) :
    ∀ᶠ r in trail,∀ (a:Axis)(v:RG17.Free R.family d),
      homogeneous F J Z r d (reflect (R:=R) d a v)=
        S.adj F.room.kernel.spin d a (homogeneous F J Z r d v) := by
  have ready:=WilsonReportingMeasuredAdmission.present F J run.leading run.obeys
  filter_upwards [ready.scheme F _ d] with r he a v
  let A:=WilsonPositionPrescribedScreen.correction F J Z.store d r
  let B:=WilsonPositionHomogeneousFrame.turn F J Z d r
  change J r d (transformed (R:=R) A (transformed (R:=R) B (reflect (R:=R) d a v)))=
    S.adj F.room.kernel.spin d a (J r d (transformed (R:=R) A (transformed (R:=R) B v)))
  rw [respects,respects]
  let laws:=Maxwell.Free.gear_laws R.family.labels
  unfold reflect Table.adj
  simp only [LinearMap.comp_apply]
  rw [←he.real,←laws.signed d,he.axis]
  exact F.phase.transport.spots.signed _ _ _

end YM.Integration.WilsonViewerGridReflection
end

