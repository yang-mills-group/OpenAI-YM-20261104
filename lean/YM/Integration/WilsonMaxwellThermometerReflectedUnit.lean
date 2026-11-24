import YM.Integration.WilsonMaxwellThermometerReflectedStation
/-! An absent reflected socket is the genuine unit on the group field and
also the plain scalar of its original normalized report, with no engineering pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedUnit
open Filter Function Finset MeasureTheory Lattice Labels Wilson RG RG.Supply Precision Next.Foundations
open Table Climb Next.UVStress Next.Rank Next.Rank.Price RG17 RG16 RG16.Literal RG12
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Trace Trace.Pilot XSpace XSpace.Normalize Maxwell Source
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Mer
open WilsonPositionProgramReportedField (entire)
open WilsonPositionThermometerCapStation (Group index)
open WilsonMaxwellThermometerReflectedPhysicalColumns (height levels atCut currency)
open WilsonMaxwellThermometerReflectedStation (Name phase)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}

private theorem unit_report (C:Family G)(made:C.Makes)(d m N p:ℕ)
    (aged:C.ref d ≤ m)(live:m ≤ N):
    awake C d m N p (C.book.scalar d)=(C.labels.level d).e0:=by
  have report:=made.calibrated d N p (aged.trans live)
  have top:(C.factory d N p).terminal.symm (C.refUnit d)=unitVec (C.labels.level d) C.path N:=by
    apply (C.factory d N p).terminal.injective
    rw [LinearEquiv.apply_symm_apply,← report.reads,report.unit_coord (C.ref d) le_rfl (aged.trans live)]
  change (((C.S.a m:ℂ)^d)⁻¹) • ((C.factory d N p).entries m
    ((C.factory d N p).terminal.symm (C.refUnit d))).x=(C.labels.level d).e0
  rw [top,report.unit_coord m aged live]
  change (((C.S.a m:ℂ)^d)⁻¹) • (((C.S.a m:ℂ)^d) • (C.labels.level d).e0)=(C.labels.level d).e0
  rw [smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos m).ne')),one_smul]

theorem paid (d m N p:ℕ)(aged : R.family.ref d ≤ m)(live : m ≤ N):
    entire R d m (N,p) (awake R.family d m N p (R.family.book.scalar d))=(R.family.labels.level d).e0:=by
  rw [unit_report R.family R.makes d m N p aged live]
  exact (R.family.labels.level d).scaled_unit _

theorem original (A:Group R.family 6)(checked:A.station.checked f H A.horizon)
    (fixed:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j)
    (d:Fin 2→ℕ)(fit:∀i,levels i<d i):
    ∀ᶠ z:ℕ×ℕ in f.fuse,∀(a:Axis)(b:Sec G 6)(n:Name)(i:Fin 2),i∉n.2.2 →
      let F:=R.family.labels.level (levels i)
      currency R A a b n.1 n.2.2 A.station.k z.1 z.2 i=F.e0 ∧
      (∀o:Site (R.family.side z.1 z.2),R.family.O z.1 z.2
        (atCut R A a b n.1 n.2.2 z.1 z.2 i) o=1) ∧
      ∀v,WilsonMaxwellThermometerReflectedStation.source R d fit A a b A.station.k n z.1 z.2 i v=
        if rankS v.val.2=0 then PowerSeries.C ((F.e0 v.val.1).re) else 0:=by
  filter_upwards [WilsonMaxwellThermometerReflectedStation.vacancy R A checked fixed,
    large_mesh f (A.station.k+1)] with z paid top
  intro a b n i blank F
  obtain ⟨eq,original⟩:=paid a b n i blank
  have age:R.family.ref (levels i)≤A.station.k:=checked.early (index A (height i))
  have cash:currency R A a b n.1 n.2.2 A.station.k z.1 z.2 i=F.e0:=by
    unfold currency
    rw [eq]
    exact WilsonMaxwellThermometerReflectedUnit.paid R (levels i) _ _ _ age (by omega)
  refine ⟨cash,original,fun v=>?_⟩
  unfold WilsonMaxwellThermometerReflectedStation.source WilsonMaxwellThermometerReflectedPhysicalColumns.issued
    WilsonPositionProgramSubmittedCoordinates.submitted
  simp only [cash,phase,blank,false_and,if_false,Complex.reCLM_apply]
end YM.Integration.WilsonMaxwellThermometerReflectedUnit
