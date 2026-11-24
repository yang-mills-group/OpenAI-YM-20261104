import YM.Integration.WilsonCapturedPrimaryWardRetimed

/-! Retain the original reporter when the weak and separated dates can occur in either order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardRelay
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical OPE MergeProof Push Local Extra.Trajectories
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address Copper
open WilsonThermometerOffsetTrajectory WilsonCapturedPrimaryWardRetimed
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {D:Rail C} {B:ℕ → ℕ → ℝ} {N p d k m:ℕ} {h:C.Makes}
    {sites:∀i,Bud C p i} {V:Sight C d p} {r:Emblems C d}

theorem original (t:Enrolled h D B m N p d sites V r) (kn:k ≤ N) (mn:m ≤ N) (wake:Awake D B k d)
    {L:ℝ} (large:1 ≤ L) (forward:C.S.a k/C.S.a m ≤ L) (back:C.S.a m/C.S.a k ≤ L)
    (on_k:∀j (v:k ≤ j),stringCost C v ≤ C.S.a k/C.S.a j)
    (on_m:∀j (v:m ≤ j),stringCost C v ≤ C.S.a m/C.S.a j):
    ∃ (V':Sight C d p) (r':Emblems C d),Enrolled h D B k N p d sites V' r' ∧
      ∃send:Palette C d → Palette C d,∀y,reading (p:=p) r mn (send y)=reading (p:=p) r' kn y ∧
          size (send y) ≤ L^(d+1)*size y:=by
  classical
  rcases le_total k m with km|mk
  · obtain ⟨V',r',record,agrees⟩:=WilsonCapturedPrimaryWardRoute.extend t mn km wake
    refine ⟨V',r',record,lift r' km,fun y=>⟨?_,?_⟩⟩
    · have later:=WilsonCapturedPrimaryWardRoute.same mn (fun j hj=>(agrees j hj).1)
      unfold reading
      rw [←later]
      exact lift_read km mn y
    · apply (lift_price record (le_refl k) km mn y).trans
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_left₀ (div_pos (C.S.a_pos _) (C.S.a_pos _)).le forward _)
        ((on_k m km).trans forward) (zero_le_one.trans (Many.stampCosts km)) (pow_nonneg (zero_le_one.trans large) _)) (size_ge _)
  · refine ⟨V,r,WilsonCapturedPrimaryWardRoute.restrict t mk,descend r mk,fun y=>⟨descend_read mk kn y,?_⟩⟩
    apply (descend_price t (le_refl m) mk kn y).trans
    exact mul_le_mul_of_nonneg_right (((on_m k mk).trans back).trans (le_self_pow₀ large (Nat.succ_ne_zero d))) (size_ge _)

end YM.Integration.WilsonCapturedPrimaryWardRelay
