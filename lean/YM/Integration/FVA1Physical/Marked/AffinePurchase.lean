import YM.Integration.FVA1Physical.Marked.PhysicalForced
import YM.RGComparison01.Ports

/-! Buy the distinguished regular-row contraction on the SAME M7a
schedule, for every permitted input subarray at each physical step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Lattice RG Wilson Pressure Tree Precision Push PriceCompiler RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AnalyticBridge VerifiedReset
open Progress.DirectedRecipe Height Roof Extra.Iteration Time ThroughLaunch Roost JointLoad
open RGComparison01 Qlocal
open scoped BigOperators Classical Topology

def AffineReserve (G : Gauge) (slope : ℕ → ℝ) : Schedule.Goal G :=
  fun _ _ _ F => (Quests.zest G slope).atFactor F

/-- The primitive scale and delay estimates for the genuine affine-null
contraction can be purchased jointly with any other obtainable schedule
goal. They make no use of the post cost selected after the delay. -/
theorem obtain_affine {G : Gauge} (hG : G.Simple) (slope : ℕ → ℝ) (positive : ∀ i, 0 < slope i) :
    Schedule.Obtainable (AffineReserve G slope) := by
  intro s T C z R E _
  obtain ⟨u,hU⟩ := Quests.altitudes s _ E
  obtain ⟨v,hV⟩ := Quests.progresses slope positive z s
  refine ⟨u ⊔ v, fun L hh D w α J K _ _ p hp θ H V => ?_⟩
  obtain ⟨X,hX,hΓ⟩ := Quests.gates J (s:=ThroughLaunch.raise s L) (u:=u)
    (show Quests.Altitude (ThroughLaunch.raise s L) (ThroughLaunch.bearing s T) E u from hU)
    (fun i=> ((sup_le_iff.mp hh).1 i).trans (D.large i).need) V
  obtain ⟨Y,hY,hK⟩ := Quests.subscriptions J z (Roof.rays s) mile C H hG hp
    (fun i j=> by unfold Roof.rays; have h := (s.profile j).price_pos; linarith) X
  refine ⟨Y,hX.trans hY,fun Z he _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ?_⟩
  exact ⟨hΓ _ (hY.trans he),hK _ he,hV L (sup_le_iff.mp hh).2 D⟩
end YM.Integration.FVA1Physical.Marked
