import YM.Integration.WilsonReportPrescribedTests
import YM.Integration.WilsonReportPhysicalFrame
import YM.Pier.Lair.Bank

/-! The independently prescribed position fields on the actual RG17
reporting stop. All inputs stay on the original physical Final and frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportPrescribedFrame
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

/-- The issued alignment and leading measurements certify this very same tower. -/
theorem present (F : Spec.Final R.family f S) (J : ℝ→PhysMS.tower S)
    (H : PhysMS.Leading F J) {K : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F K (J r) d) :
    Pier.Lair.Present F J := by
  refine ⟨?_,WilsonReportPrescribedTests.measured F J H⟩
  intro m
  have cuts (i j : Fin (m+1)) : ∀ᶠ r in RG17.home,∀ h : i.val≤j.val,∀ x,
      J r j ((Maxwell.Free.scheme R.family.book.grid).rise h x)=F.sector.derivatives.rise h (J r i x) := by
    by_cases h : i.val≤j.val
    · exact (H.raised h).mono fun _ row _ => row
    · exact Eventually.of_forall fun _ h' => (h h').elim
  filter_upwards [eventually_all.mpr (fun i : Fin (m+1) => paid i),
    eventually_all.mpr (fun i => eventually_all.mpr (cuts i))] with r yes joined
  exact ⟨yes,joined⟩

/-- Actual window width in the exact currency required by the prescribed
position-field buyer. -/
theorem comparable (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B) :
    RG17.Panoramic.Comparably R (WilsonMeasuredWindow.stop R.family.path.levels hG B) := by
  let A := R.family.path.levels
  let m := WilsonMeasuredWindow.stop A hG B
  let f : ℝ := 3^(B+1)
  have fp : 0<f := by dsimp [f]; positivity
  have grows := Real.tendsto_log_atTop.comp (Station.hat_rate A hG)
  have cheap := ((Real.isLittleO_pow_exp_atTop (n:=B+1)).comp_tendsto grows).bound (inv_pos.mpr fp)
  have fits : ∀ᶠ k : ℕ in atTop,RG16.Lambda A k^(B+1)≤A.clock.hatBeta k := by
    filter_upwards [grows.eventually_ge_atTop 1,cheap] with k high upper
    let b := A.clock.hatBeta k
    let l := Real.log b
    have one : 1≤l := high
    have bpos : 0<b := zero_lt_one.trans (A.fits.delayed k)
    change ‖l^(B+1)‖≤f⁻¹*‖Real.exp l‖ at upper
    rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans one) _),Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_log bpos] at upper
    change (2+l)^(B+1)≤b
    calc
      _ ≤ (3*l)^(B+1) := pow_le_pow_left₀ (by linarith) (by linarith only [one]) _
      _ = f*l^(B+1) := mul_pow ..
      _ ≤ b := by simpa only [←mul_assoc,mul_inv_cancel₀ fp.ne',one_mul]
        using mul_le_mul_of_nonneg_left upper fp.le
  obtain ⟨ranks,window⟩ := WilsonFundedMeasuredWindow.all_radii R pace hG hB
  have short : ∀ᶠ r : ℝ in RG17.home,r<R.family.S.a 0 := (gt_mem_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds
  filter_upwards [RG17.positiveLength,short,ranks.eventually fits] with r hr small upper
  have a := R.family.S.a_pos (m r)
  have price := window r hr small.le
  have Bx := A.fits.delayed (m r)
  have base : 1≤RG16.Lambda A (m r) := by change (1:ℝ)≤2+Real.log _; linarith [Real.log_nonneg Bx.le]
  have l : 1≤r/R.family.S.a (m r) := (one_le_pow₀ base).trans price.1
  refine ⟨?_,?_⟩
  · simpa only [one_mul] using (le_div_iff₀ a).mp l
  have upper' := price.2.trans (upper.trans (le_self_pow₀ Bx.le (by norm_num : (2:ℕ)≠0)))
  simpa only [mul_comm] using (div_le_iff₀ a).mp upper'

/-- Before every period, the original independent J(r) admits actual
regulated Wilson representatives on the selected physical stop. -/
theorem selected (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (original : FundedOriginalProperties.{u} hG δ W)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f S) (fac : OPE.Facilities R.family f S)
    (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J) {K : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F K (J r) d) :
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
      L.shift=(fun _ _ => LinearEquiv.refl ..) ∧
      (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L J) d) ∧
      ∀ d : ℕ, ∃ e : ℕ,∀ᶠ r in RG17.home,let k := L.level r
        ∀ v : RG17.Free R.family d,∃ w : R.family.label d, master L d r w=J r d v ∧
        ∀ N p : ℕ,k≤N → Spindle.paid R.family d k N p (RG17.atRef L d r (N,p) w) ≤
          R.family.path.levels.clock.hatBeta k^e*‖v‖ := by
  obtain ⟨u,Q,L,hU,pegs,level,shift,_⟩ := WilsonReportPhysicalFrame.selected hG W original pace hB F fac
  have near : RG17.Panoramic.Comparably R L.level := level ▸ comparable hG pace hB
  have price := fun d => Pier.Lair.prices F (present F J H paid) d Q fac.toServices L pegs near
  refine ⟨u,Q,L,hU,pegs,level,shift,price,?_⟩
  intro d
  obtain ⟨e,table⟩ := (price d).affordability
  refine ⟨e,?_⟩
  filter_upwards [table,pegs.level.growing.eventually_ge_atTop (R.family.ref d)] with r row refs
  dsimp only
  intro v
  obtain ⟨w,cost,field⟩ := row.1 v
  refine ⟨w,field,?_⟩
  intro N p visible
  rw [WilsonReportRegulatedSmear.reference L r d w refs visible]
  exact cost

end YM.Integration.WilsonReportPrescribedFrame
end

