import YM.Integration.WilsonPhysicalHistoryGroupedRegularReturn
import YM.Integration.WilsonPhysicalHistoryGroupedForcedReturn

/-! The actual earlier marked density in the original turning-step coordinates.
The multiplicative constant is the full marker polynomial from the clear
rows. The same singleton and quiet forcing partners enter the same gas. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGalleryRestore
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryCorrectionCarton
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] [Fintype V] [Countable I]
  {G : Gauge} {n : Side} {Z : Census V} {P : Rep G n} {o : V → Site n}
  (A : Gallery T I o P Z) (w : V → ℝ) (positive : ∀ v, 0 < w v)

include positive in
theorem original {a q h : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid w P.p.B (a+2) q)
    (hard : A.K.Paid w P.p.B a h) (t : T) (U : Config G n) :
    A.density t U = Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) *
      restore P (WilsonPhysicalHistoryGroupedRegularReturn.single A t)
        (WilsonPhysicalHistoryGroupedForcedReturn.single A t) (regular A t) (forced A t) U := by
  have more : 0 ≤ a+2 := by linarith
  have gas := WilsonPhysicalHistoryGroupedGas.gas A w positive expo hard t U
  have modes := WilsonPhysicalHistoryGroupedRegularReturn.original A w positive more reg t U
  have boxes := funext (fun box =>
    WilsonPhysicalHistoryGroupedForcedReturn.original A w positive expo hard t box U)
  unfold Gallery.density restore
  rw [gas, WilsonPhysicalHistoryGroupedClear.factored A.E w positive more reg t U, modes, boxes]
  rw [mul_smul_comm, mul_assoc]

end YM.Integration.WilsonPhysicalHistoryGalleryRestore
end

