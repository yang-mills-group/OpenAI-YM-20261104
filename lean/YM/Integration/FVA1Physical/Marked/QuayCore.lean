import YM.LocalLTE.Quay.Core

/-! Defects in positive-grade field coordinates are compared using the true
calibrated change of basis, including different engineering units on the two
sides. This also bounds the recurrence error of a prescribed pair of forecasts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.Quay
open Lattice RG Source Labels Extra.Histories LocalLTE Bid
variable {G : Gauge} {d N n m : ℕ} {F : Frame G d} (H : History G) (W : Worth)
  (P : Voice F H n (m+1)) (Q : Voice F H n m) {A : Hol G} (D : SectionData F)
  (hp : Heard D H N n A (m+1) P) (hq : Heard D H N n A m Q)
  (step : Responds D H N n W m P Q) (bank : Bank W H.levels)

include hp hq step bank

/-- The fine forecast is advanced with the true purchased preimage and the
true outgoing coordinate map. Unit leakage is projected out only *after* this
map. No equality between the incoming and outgoing test frames is assumed. -/
theorem forecast_transport (x u v : F.Coeff) {ef ec : ℝ}
    (fine : ‖Sail.sampleNorm H N d (m+1)‖ * F.coeffSize (P.index x-u) ≤ ef)
    (coarse : ‖Sail.sampleNorm H N d m‖ * F.coeffSize (Q.index x-v) ≤ ec) :
    ‖Sail.sampleNorm H N d m‖ * F.coeffSize (F.core (Q.index (P.index.symm u)-v)) ≤ 1/2 * ef + ec := by
  let a := Q.index (P.index.symm u)
  let b := Q.index x
  let c := ‖Sail.sampleNorm H N d m‖
  have hn : 0 ≤ c := norm_nonneg _
  have h0 : c * F.coeffSize (F.core (b-a)) ≤ 1/2 * (‖Sail.sampleNorm H N d (m+1)‖ * F.coeffSize (F.core (P.index x-u))) := by
    simpa only [a,b,c,map_sub,LinearEquiv.apply_symm_apply] using (Concourse.forwardT H W P Q D hp hq step bank (x-P.index.symm u)).1
  have hf : c * F.coeffSize (F.core (b-a)) ≤ 1/2 * ef := by
    refine h0.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact (mul_le_mul_of_nonneg_left (Work.G08.size_core F _) (norm_nonneg _)).trans fine
  have hc : c * F.coeffSize (F.core (b-v)) ≤ ec :=
    (mul_le_mul_of_nonneg_left (Work.G08.size_core F _) hn).trans coarse
  have rev : F.coeffSize (F.core (a-b)) = F.coeffSize (F.core (b-a)) := by
    simpa only [map_sub] using Work.G08.size_sub_rev F (F.core a) (F.core b)
  change c * F.coeffSize (F.core (a-v)) ≤ _
  calc
    _ = c * F.coeffSize (F.core (a-b)+F.core (b-v)) := by rw [← map_add,sub_add_sub_cancel]
    _ ≤ c * (F.coeffSize (F.core (a-b)) + F.coeffSize (F.core (b-v))) :=
      mul_le_mul_of_nonneg_left (Size.add F _ _) hn
    _ = c * F.coeffSize (F.core (b-a)) + c * F.coeffSize (F.core (b-v)) := by rw [rev,mul_add]
    _ ≤ _ := add_le_add hf hc

end YM.Integration.FVA1Physical.Marked.Quay
