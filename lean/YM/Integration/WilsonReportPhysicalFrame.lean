import YM.Integration.WilsonReportCashierLimit
import YM.RG17.Canvas
import YM.RG17.Pitch

/-! Select one original RG17 reporting layout at the funded physical stop.
Its actual continuum frame has representatives whose true incoming Spindle
charges are paid before every period and fine cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportPhysicalFrame
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram
open PhysicalNext.Repeat.Legato WilsonLimitConstruction
open WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical
universe u
variable {G : Gauge} {R : Run G}

theorem reached (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) : Reach R.family (WilsonMeasuredWindow.stop R.family.path.levels hG B) := by
  have h := WilsonMeasuredWindow.measured_stop_height R.family.path.levels hG B
    (WilsonFundedMeasuredWindow.paced R pace) hB RG17.ageLarge RG17.lengthRate
  exact ⟨WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB,h.pace⟩

/-- One genuine reporting chart serves all valences. On it every physical
frame vector has a preselected exact representative, and its genuine finite
charge is bounded on every visible cutoff and period, independently of
the vector, test, and the deadlines for connected expansions. -/
theorem selected (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S)
    (fac : OPE.Facilities R.family f S) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      L.shift=(fun _ _ => LinearEquiv.refl ..) ∧
      ∀ d : ℕ, ∃ e : ℕ,∀ᶠ r in RG17.home,let k := L.level r
        ∀ v : RG17.Free R.family d,∃ w : R.family.label d, master L d r w=L.frame d r v ∧
        ∀ N p : ℕ,k≤N → Spindle.paid R.family d k N p (RG17.atRef L d r (N,p) w) ≤
          R.family.path.levels.clock.hatBeta k^e*‖v‖ := by
  let C := R.family
  let u := Ultrafilter.of f.fuse
  have hu : (u:Filter UVIndex)≤f.fuse := Ultrafilter.of_le _
  obtain ⟨Q⟩ := Lenses.attains_mantle17 F fac.toServices u hu original.2.1.coverage
  obtain ⟨L,level,shift,pegs⟩ := RG17.installed (B:=Q) hu _ (reached hG pace hB) (fun _ _ => LinearEquiv.refl ..)
  refine ⟨u,Q,L,hu,pegs,level,shift,?_⟩
  intro d
  refine ⟨Lenses.price d+1,?_⟩
  have up := (Station.hat_rate C.path.levels hG).comp pegs.level.growing
  filter_upwards [RG17.engineeringPass Q L fac.toServices pegs d,pegs.level.growing.eventually_ge_atTop (C.ref d),
      up.eventually_ge_atTop 2] with r fee hr htwo
  dsimp only
  intro v
  obtain ⟨w,receipt,field⟩ := fee.1 v
  have equal : L.shift d r w=w := by rw [shift]; rfl
  refine ⟨w,?_,?_⟩
  · change RG12.engineering L.charts d (L.level r) (L.shift d r w)=_
    rw [equal]; exact field
  intro N p hk
  rw [WilsonReportRegulatedSmear.reference L r d w hr hk,equal]
  let b := C.path.levels.clock.hatBeta (L.level r)
  change mass C d w ≤ b^(Lenses.price d+1)*‖v‖
  have growth : 2*b^Lenses.price d ≤ b^(Lenses.price d+1) := calc
    _ ≤ b*b^Lenses.price d := mul_le_mul_of_nonneg_right htwo (pow_nonneg (zero_le_two.trans htwo) _)
    _ = _ := (mul_comm b (b^Lenses.price d)).trans (pow_succ b (Lenses.price d)).symm
  exact receipt.trans (mul_le_mul_of_nonneg_right growth (norm_nonneg _))

end YM.Integration.WilsonReportPhysicalFrame
end

