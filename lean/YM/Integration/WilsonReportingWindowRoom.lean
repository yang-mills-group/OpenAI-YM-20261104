import YM.Integration.WilsonMasterCoordinatePrice
import YM.Integration.WilsonReportingLength
import YM.PhysMS.Foundation.Estimates

/-! A radius-independent price for the full short-distance reporting interval
on one physical family, chosen before the cutoff and the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingWindowRoom
open Function Set Filter Lattice Wilson RG OPE Spec PhysMS Trace.Pilot
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) (B : ℝ)

def values (z : ℝ → ℝ) (m : ℕ) : Set ℝ :=
  insert 1 ((fun r => ‖z r‖) '' Icc (C.S.a m) (WilsonReportingLength.radius C B m))

def envelope (z : ℝ → ℝ) (m : ℕ) : ℝ := sSup (values C B z m)

private theorem upper {z : ℝ → ℝ} (hz : RateLE trail LogV z 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ s ∈ values C B z m, s ≤ Real.exp (η*C.S.scale m) := by
  obtain ⟨δ,hδ,hnear⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hz η hη)
  filter_upwards [(WilsonReportingLength.fine C B).eventually (Ioc_mem_nhdsGT hδ),
    C.S.divergent.eventually_ge_atTop 0] with m hm hT
  intro s hs
  rcases hs with hs|⟨r,hr,rfl⟩
  · rw [hs]
    exact Real.one_le_exp (mul_nonneg hη.le hT)
  · have pos := (C.S.a_pos m).trans_le hr.1
    have bound : ‖z r‖ ≤ Real.exp (η*LogV r) := hnear ⟨pos,hr.2.trans hm.2⟩
    exact bound.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.log_le_log (inv_pos.mpr pos) (inv_anti₀ (C.S.a_pos m) hr.1)) hη.le))

theorem uniform {z : ℝ → ℝ} (hz : RateLE trail LogV z 0) :
    RateIs atTop C.S.scale (envelope C B z) 0 ∧ ∀ᶠ m in atTop,
      ∀ r ∈ Icc (C.S.a m) (WilsonReportingLength.radius C B m), ‖z r‖ ≤ envelope C B z m := by
  have bounded : ∀ᶠ m in atTop, BddAbove (values C B z m) :=
    (upper C B hz one_pos).mono fun m hm => ⟨_,hm⟩
  have lo : ∀ᶠ m in atTop, 1 ≤ envelope C B z m :=
    bounded.mono fun m hm => le_csSup hm (mem_insert ..)
  have cost : RateLE atTop C.S.scale (envelope C B z) 0 := by
    intro η hη
    filter_upwards [upper C B hz hη,lo] with m hm hl
    rw [Real.norm_of_nonneg (zero_le_one.trans hl)]
    exact csSup_le ⟨1,mem_insert ..⟩ hm
  refine ⟨RateIs.of_sandwich (RateIs.const (c:=1) C.S.divergent one_pos) cost lo
    (Eventually.of_forall fun _ => le_rfl) C.S.divergent,?_⟩
  filter_upwards [bounded] with m hm
  intro r hr
  exact le_csSup hm (mem_insert_of_mem _ ⟨r,hr,rfl⟩)

end YM.Integration.WilsonReportingWindowRoom
