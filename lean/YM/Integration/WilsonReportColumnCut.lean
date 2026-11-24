import YM.Integration.WilsonReportRegularMoments

/-! The genuine finite local insertion associated to each funded regular
reporting column, including its true gauge support and its uniform spatial
truncation on the original coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportColumnCut
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Cells
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26
open RG12 RG17 RG17.Panoramic SharpGram Next.UVStress Extra.Histories
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol OPE.Strobe.Panoramic Push.GridApprox
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} {F:Spec.Final R.family f S}

def localized (L : Layout F) (r : ℝ) (d k N p : ℕ) (b : R.family.label d) (x : Site (R.family.side k p)) :=
  bead R.family d k N p (R.family.path.levels.budget k).B (atRef L d r (N,p) b) x

/-- Every support and every coefficient occurs on the original family at
the indicated physical period. -/
theorem field (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (L : Layout F) (E : OPE.Services R.family f S) (r : ℝ) {d k N p t : ℕ} (b : R.family.label d)
    (grade : R.family.ref d ≤ L.level r) (zero : R.family.ref 0 < k) (deep : L.level r ≤ k) (cut : k < N)
    (zoom : R.family.S.a (L.level r)/R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k^t)
    (x : Site (R.family.side k p)) :
    let C := R.family
    let B := (C.path.levels.budget k).B
    let a := C.path.levels.clock.hatBeta k^(1+t*(d+1))*mass C d (L.shift d r b)
    let U₀ := regularRead C d k N p (atRef L d r (N,p) b) x
    let U₁ := localized L r d k N p b x
    Interior (window x (omen C d k B)) U₁ ∧ Envelope U₀ ∧ Envelope U₁ ∧ ∀ U,
      ‖U₀ U‖ ≤ 3*a ∧ ‖U₀ U-U₁ U‖ ≤ 2*(Real.exp (-2*(B:ℝ))*a) ∧ ‖U₁ U‖ ≤ 5*a := by
  obtain ⟨citizen,book⟩ := WilsonReportCitizenRun.on_run hG W funding subsidy
  obtain ⟨σ,χ,tune⟩ := OPE.Yarn.enroll citizen.toSharper R.makes hG
  have fare := WilsonReportRegularMoments.transported (p:=p) L E r b grade deep cut.le zoom
  have price := enamelCost tune citizen x (grade.trans deep) zero cut _ fare
  have support := bead_local tune x (atRef L d r (N,p) b) (grade.trans deep) cut.le (R.family.path.levels.budget k).B
  dsimp only
  refine ⟨support,price.1,price.2.1,?_⟩
  intro U
  have cap (y : ℝ) (hy : 0 ≤ y) :
      ((R.family.path.levels.params k).columns : ℝ)*y ≤ R.family.path.levels.clock.hatBeta k*y :=
    mul_le_mul_of_nonneg_right (book.money.present k) hy
  have upper := cap _ ((paid_pos ..).trans fare)
  rw [pow_add,pow_one,mul_assoc]
  exact ⟨(price.2.2 U).1.trans (mul_le_mul_of_nonneg_left upper (by norm_num)),
    (price.2.2 U).2.1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left upper (Real.exp_nonneg _)) (by norm_num)),
    (price.2.2 U).2.2.trans (mul_le_mul_of_nonneg_left upper (by norm_num))⟩

end YM.Integration.WilsonReportColumnCut
end

