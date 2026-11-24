import YangMills.WilsonProof.NativeSupport.OriginalPointReturns
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFixedStencils
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.PhysicalPeriodNodes
open YangMills YangMills.Wilson
open YM.Extraction YM.FullVolume
open Filter Function Set MeasureTheory
open scoped Topology ContDiff
variable {g : GaugeGroup} (C : YM.Family g.core)

def representatives {N m n : ℕ}
    (x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N)) : Positions n :=
  fun i a => ZMod.valMinAbs (x i a)

theorem placed {N m n : ℕ}
    (x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N)) :
    tag (C.S.a N) (representatives C x) = nodePosition (wilsonFamily C) N m x := rfl

theorem moment {N m n : ℕ} (v : Fin n → C.book.Token)
    (x : Fin n → Site ((wilsonFamily C).period m * (wilsonFamily C).denominator N)) :
    lifted C N m v (representatives C x) = (wilsonFamily C).finiteMoment N m v x := by
  rw [moment_eq]
  unfold lifted
  congr 1
  funext i a
  exact ZMod.coe_valMinAbs _

theorem safe {n m : ℕ} {z : YM.Points n}
    (hz : z ∈ periodPatch (wilsonFamily C) m n) : z ∈ NoHit C.S m n :=
  (no_wrap_hit C.S (show z ∈ Inside C.S m n from hz.2)).2 hz.1

def appoint (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ) :
    PeriodPointTable (wilsonFamily C) :=
  fun m {n} v z => row m n v z.val

theorem appointment (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ)
    (m n : ℕ) (v : Fin n → C.book.Token) {z : YM.Points n} (hz : z ∈ periodPatch (wilsonFamily C) m n) :
    periodValue (appoint C row) m v z = row m n v z := by
  simp [periodValue, hz, appoint]

theorem test (row : (m n : ℕ) → (Fin n → C.book.Token) → YM.Points n → ℂ)
    (m n : ℕ) (v : Fin n → C.book.Token) (t : SeparatedTest n) (s : (wilsonFamily C).suitable m t) :
    YM.Test.applyTo t (row m n v) = ∫ z, t z * periodValue (appoint C row) m v z := by
  apply integral_congr_ae
  filter_upwards with z
  change t z * row m n v z = t z * periodValue (appoint C row) m v z
  by_cases hz : z ∈ tsupport t
  · exact congrArg (fun a : ℂ => t z * a) (appointment C row m n v ⟨t.tsupport_subset hz,s hz⟩).symm
  · have zero : t z = 0 := notMem_support.mp (fun h => hz (subset_closure h))
    simp [zero]

end IssuedBridge.PhysicalPeriodNodes
end
