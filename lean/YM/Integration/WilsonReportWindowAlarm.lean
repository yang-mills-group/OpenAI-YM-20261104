import YM.Integration.WilsonReportWindowSource
import YM.Integration.WilsonPhysicalMarkedDefectInteriorHot

/-! Remove the actual failed primary of a deposited source window in its
original fitted units; no product of independent alarms is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowAlarm
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Vitrines Extra.Histories
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonPhysicalMarkedDefect WilsonReportWindowSource
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G}

/-- The entire fitted failed primary, including its true spatial translation.
For each arity/grade and perturbative order the clock is chosen before all
fine cutoffs, periods, incoming fine fields, growing labels and positions. -/
theorem physical (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (d q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ,k≤N → ∀ p (v : R.family.label d) (x : Site (R.family.side k p)),
    ∫ U,‖alarm R.family (N:=N) v x U‖ ∂(Therm.scene R.family.path N p k) ≤
      ε*Spindle.paid R.family d k N p v*(regulatorRun R.family N p k)^q := by
  obtain ⟨citizen,_⟩ := WilsonReportCitizenRun.on_run hG W funding subsidy
  have thermal := InteriorHot.all_orders R hG citizen.safeguards d 0 q hε
  filter_upwards [thermal] with k bound N cut p v x
  let C := R.family
  let Q := parcel C d k N p v
  let a := (C.labels.level d).coeffSize Q.x
  let α := alto C.path k d
  let f := StoredInterior.failed C N p d k Q
  let μ := Therm.scene C.path N p k
  have fee := bound N cut p Q a le_rfl 0 le_rfl k le_rfl
  have law : C.Makes := R.makes
  have base : actualTransport C (N:=N) (p:=p) f (le_refl k)=f := actualTransport_base C law cut f
  have original : (∫ U,‖f U‖ ∂μ) ≤ ε*a*(regulatorRun C N p k)^q := by
    simp only [pow_zero,inv_one,one_smul] at fee
    change (∫ U,‖actualTransport C (N:=N) (p:=p) f (le_refl k) U‖ ∂μ) ≤ ε*a*(regulatorRun C N p k)^q at fee
    rwa [base] at fee
  have moved : (∫ U,‖f (pull 1 x U)‖ ∂μ)=(∫ U,‖f U‖ ∂μ) :=
    Therm.retune law.wilson 1 x cut (fun U=>‖f U‖)
  change (∫ U,‖α*f (pull 1 x U)‖ ∂μ) ≤ _
  simp_rw [norm_mul]
  rw [integral_const_mul,moved]
  calc
    _ ≤ ‖α‖*(ε*a*(regulatorRun C N p k)^q) := mul_le_mul_of_nonneg_left original (norm_nonneg _)
    _ = _ := by rw [mintedLabel]; dsimp only [α,a,Q,C]; ring

end YM.Integration.WilsonReportWindowAlarm
end

