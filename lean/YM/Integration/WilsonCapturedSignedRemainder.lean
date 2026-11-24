import YM.Integration.WilsonCapturedGermCounterterm
import YM.Trace.Physicalv2.GermSplit

/-! Subtract the unique calibrated physical counterterm as an actual
field. Its residual has exactly zero periodic germ; its stored head is
bounded by the wrapping invoice rather than set to zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedSignedRemainder
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d : ℕ)

theorem purchased (hG : G.Simple) :
    ∀ᶠ u : ℕ in atTop, ∀ p N, u ≤ N →
      ∀ (q : Coefficient (R.family.labels.level d) (R.family.side u p)) {r : ℝ},
        reads (C:=R.family) d N p u q r →
        ∃ (s : Coefficient (R.family.labels.level d) (R.family.side u p)) (x : R.family.label d),
          let π := page (C:=R.family) d p u
          let cost := r + (2 * stock R.family u) * (R.family.labels.level d).coeffSize (π q)
          π s = 0 ∧ π ((R.family.factory d N p).entries u x) = π q ∧
          reads (C:=R.family) d N p u s cost ∧
          value (C:=R.family) d N p u q - calValues (C:=R.family) d N p u x =
            value (C:=R.family) d N p u s ∧
          (R.family.labels.level d).coeffSize s.x ≤ invoice (C:=R.family) d u p * cost := by
  filter_upwards [open_late R.family hG d] with u opening
  intro p N hN q r paid
  obtain ⟨s,x,hs,hzero,actual,hx⟩ := fresh_split0 (d:=d) (N:=N) (p:=p) (i:=u) R.makes (opening p) hN q paid
  have head := measured_diff d N p u R.makes (opening p).post hN hs
  rw [hzero,zero_sub,count_neg] at head
  refine ⟨s,x,hzero,?_,hs,?_,head⟩
  · exact (fitting_apply d N p u R.makes (opening p) hN x).symm.trans hx
  · exact sub_eq_iff_eq_add.mpr actual

end YM.Integration.WilsonCapturedSignedRemainder
