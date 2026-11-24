import YM.Integration.WilsonReportWindowAlarm

/-! The genuine polynomial and retained masked source are bounded even on
the original failed configurations. This permits products without independence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowEnvelope
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Strobe.Panoramic OPE.Vitrines Extra.Histories Extra.Multi
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonPhysicalMarkedDefect WilsonReportWindowSource
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G}

def units (C : Family G) (d k N p : ℕ) :=
  5*(C.path.levels.params k).columns +
    BasisCost.price (C.localSection d)*((regulatorRun C N p k/2)⁻¹)^(BasisCost.slots (C.labels.level d))

theorem regulated (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    {d k N p : ℕ} (v : R.family.label d) (grade : R.family.ref d≤k) (zero : R.family.ref 0<k) (cut : k<N)
    (x : Site (R.family.side k p)) :
    let C := R.family; let B := (C.path.levels.budget k).B
    let F := bead C d k N p B v x; let H := opened C (N:=N) v x; let A := alarm C (N:=N) v x
    Envelope F ∧ Envelope H ∧ Envelope A ∧ F-H=A ∧
    ∀ U, ‖F U‖ ≤ units C d k N p*Spindle.paid C d k N p v ∧ ‖H U‖ ≤ units C d k N p*Spindle.paid C d k N p v := by
  let C := R.family
  let B := (C.path.levels.budget k).B
  let D := C.labels.level d
  let Q := parcel C d k N p v
  let g := regulatorRun C N p k
  let α := alto C.path k d
  let p' := Spindle.paid C d k N p v
  let σ := BasisCost.price (C.localSection d)*((g/2)⁻¹)^(BasisCost.slots D)
  let z := (C.path.levels.params k).columns
  let X := (C.localSection d).footprint (0:Site (C.side k p))
  let θ := (C.path.rep N p k).p.threshold
  let A := alarm C (N:=N) v x
  let H := opened C (N:=N) v x
  let F := bead C d k N p B v x
  have law : C.Makes := R.makes
  obtain ⟨citizen,_⟩ := WilsonReportCitizenRun.on_run hG W funding subsidy
  obtain ⟨σ₀,χ,tune⟩ := OPE.Yarn.enroll citizen.toSharper R.makes hG
  have actual := (WilsonReportWindowSource.actual C law grade cut.le v).2.2.2 x
  have raw := enamelCost tune citizen x grade zero cut v (le_refl p')
  have ap : 0≤p' := Spindle.paid_pos C d k N p v
  have gp := RG16.Literal.g_pos law (p:=p) cut.le
  have zp : 0≤z := zero_le_one.trans (C.path.levels.params k).columns_ge
  have sp : 0 ≤ σ := mul_nonneg (zero_le_one.trans (BasisCost.price_pos _))
    (pow_nonneg (inv_nonneg.mpr (half_pos gp).le) _)
  have settled : ‖α‖*D.coeffSize Q.x=p' := (mintedLabel (C:=C) (N:=N) (p:=p) (k:=k) v).symm
  have charge (U) : ‖A U‖ ≤ σ*p' := by
    have rough := InteriorSection.failed C N p d k law cut.le Q (le_refl (D.coeffSize Q.x)) (pull 1 x U)
    have budget : ‖StoredInterior.failed C N p d k Q (pull 1 x U)‖ ≤ σ*D.coeffSize Q.x := by
      apply rough.trans
      split
      · exact mul_nonneg sp (BasisCost.coeff_nonneg _)
      · rfl
    change ‖α * StoredInterior.failed C N p d k Q (pull 1 x U)‖≤_
    rw [norm_mul,←settled]
    exact (mul_le_mul_of_nonneg_left budget (norm_nonneg α)).trans_eq (by ring)
  have measured : Measurable (StoredInterior.failed C N p d k Q) := by
    let f := StoredInterior.fitted C N p d k Q
    have hf := (InteriorSection.chart C N p d k law grade cut.le Q (le_refl (D.coeffSize Q.x))).1.borel
    change Measurable (fun U=>if Healthy θ X U then 0 else -f U)
    exact Measurable.ite (healthy_closed θ X).measurableSet measurable_const hf.neg
  have envelope : Envelope A := ⟨measurable_const.mul (measured.comp (continuous_pull ..).measurable),_,charge⟩
  have fields (U) : H U=F U-A U := eq_sub_iff_add_eq.mpr (actual U).symm
  have upper (U) : ‖F U‖≤5*(z*p') := (raw.2.2 U).2.2
  have bounded (U) : ‖H U‖≤units C d k N p*p' := by
    rw [fields]
    exact (norm_sub_le ..).trans ((add_le_add (upper U) (charge U)).trans_eq (by dsimp only [units,z,σ,g,D]; ring))
  have mh : Measurable H := by
    rw [show H=(fun U=>F U-A U) from funext fields]
    exact raw.2.1.meas.sub envelope.meas
  refine ⟨raw.2.1,⟨mh,_,bounded⟩,envelope,?_,?_⟩
  · funext U
    exact sub_eq_iff_eq_add.mpr (by rw [add_comm]; exact actual U)
  intro U
  refine ⟨(upper U).trans ?_,bounded U⟩
  change 5*(z*p')≤(5*z+σ)*p'
  nlinarith only [mul_nonneg sp ap]

end YM.Integration.WilsonReportWindowEnvelope
end

