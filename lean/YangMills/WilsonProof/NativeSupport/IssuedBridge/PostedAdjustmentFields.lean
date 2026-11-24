import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralAdjustment
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedAdjustmentFields
open YangMills YangMills.Wilson YM YM.Integration YM.Maxwell YM.Maxwell.Free WilsonLimitConstruction
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale WilsonPositionHomogeneousCoefficients
open PostedBilateralAdjustment Filter Set Function
open scoped Topology BigOperators Classical
variable {g : GaugeGroup} (Z : WilsonPrescription g.core)

theorem invertible (d : ℕ) : ∀ᶠ t : ℝ in 𝓝[>] 0, Bijective (value Z d t) := by
  filter_upwards [(WilsonPositionHomogeneousNear.invertible Z d).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t inv h
  have ht : 0 < t := h
  change Bijective (stand (limb Z d t))
  rw [positive Z d ht]
  simpa only [WilsonPositionHomogeneousNear.field,if_pos ht] using inv

theorem unit (t : ℝ) (d : ℕ) (v : (maxwellReference g).sector d) (hv : v.val = 1) :
    value Z d t v = v := by
  have eq : v = leaf g.core d := Subtype.ext hv
  subst v
  change leaf g.core d + (limb Z d t).val (leaf g.core d) = _
  rw [(limb Z d t).property.1,add_zero]

theorem original (law : Warrant Z) {t : ℝ} (ht : 0 < t) (d e : ℕ)
    (v : (maxwellReference g).sector d) (w : (maxwellReference g).sector e) (same : v.val = w.val) :
    (value Z d t v).val = (value Z e t w).val := by
  have step {a b : ℕ} (h : a ≤ b) (u : (maxwellReference g).sector a) (z : (maxwellReference g).sector b)
      (same : u.val = z.val) : (value Z a t u).val = (value Z b t z).val := by
    have place : up h u = z := Subtype.ext same
    have inc := WilsonPositionHomogeneousRealization.includes Z law h ht u
    rw [place] at inc
    simp only [value,positive Z _ ht]
    exact (congrArg Subtype.val inc).symm
  rcases le_total d e with le|le
  · exact step le v w same
  · exact (step le w v same.symm).symm
end IssuedBridge.PostedAdjustmentFields
