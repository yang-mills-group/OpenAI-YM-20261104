import YM.Integration.WilsonOriginalSupportedMixedJets
import YM.Integration.WilsonOriginalCompactlyFiledResidual
import YM.Integration.WilsonOriginalFourierReadback

/-! An actual mixed spatial withdrawal on the localized physical residual. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalLocalizedMixedSalary
open Filter Set Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb UnitAddTorus
open WilsonOriginalSupportedBoxChart
open WilsonOriginalSupportedMixedJets (derivative)
open WilsonOriginalCompactlyFiledResidual (raw)
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalTestedFourierBank (Prices)
open scoped Topology BigOperators ContDiff Classical

theorem original {G : Gauge} {u : ℝ → ℝ} (simple : G.Simple) (clock : Coupling G u)
    {d : ℕ} (l h : Space (d+1)) (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1)
    (f : ℝ → Space (d+1) → ℂ) (a : ℕ → Space (d+1) → ℂ)
    (sf : ∀ᶠ r in trail, ∀ x : Space (d+1), (∀ i, x i ∈ Icc (0:ℝ) 1) → ContDiffAt ℝ ∞ (f r) x)
    (sa : ∀ k x, (∀ i, x i ∈ Icc (0:ℝ) 1) → ContDiffAt ℝ ∞ (a k) x)
    (price : Prices u (fun r v => mFourierCoeff (localize 0 l h (f r)) v)
      (fun k v => mFourierCoeff (localize 0 l h (a k)) v))
    (p j : ℕ) (dir : ℕ → Fin (d+1)) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x : Space (d+1), (∀ i, x i ∈ Icc (0:ℝ) 1) →
      ‖derivative dir (raw l h (f r) a (u r) p) j x‖ ≤ ε*u r^p := by
  let F := fun r => raw l h (f r) a (u r) p
  have held (r : ℝ) : Supported l h (F r) := WilsonOriginalCompactlyFiledResidual.supported l h _ 
  have smooth : ∀ᶠ r in trail, ContDiff ℝ ∞ (F r) := by
    filter_upwards [sf] with r field
    apply WilsonOriginalCompactlyFiledResidual.smooth
    intro x hx
    have box (i : Fin (d+1)) : x i ∈ Icc (0:ℝ) 1 :=
      ⟨(left i).le.trans (hx i).1,(hx i).2.trans (right i).le⟩
    apply (field x box).sub
    have each (k : Fin (p+1)) : ContDiffAt ℝ ∞ (fun y => (u r:ℂ)^k.val*a k.val y) x :=
      contDiffAt_const.mul (sa k.val x box)
    exact ContDiffAt.sum (fun k _ => each k)
  let actual := fun r => if hr : ContDiff ℝ ∞ (F r) then
    WilsonOriginalSupportedMixedJets.field dir left right (F r) hr (held r) j else 0
  have paid := WilsonOriginalFourierReadback.original simple clock price p (fun k : Fin j => dir k.val)
    (fun _ => 2*(Real.pi:ℂ)*Complex.I) actual (by
      filter_upwards [smooth,sf] with r hr s v
      simp only [actual,dif_pos hr,WilsonOriginalSupportedMixedJets.field,ContinuousMap.coe_mk]
      rw [WilsonOriginalSupportedMixedJets.original dir left right (F r) hr (held r)]
      congr 1
      exact WilsonOriginalCompactlyFiledResidual.original l h (f r) a (u r) p v
        (fun i => (left i).le) (fun i => (right i).le)
        (fun x hx => (s x hx).continuousAt.continuousWithinAt)
        (fun k x hx => (sa k x hx).continuousAt.continuousWithinAt)) eps
  filter_upwards [paid,smooth] with r bound hr x hx
  have pt := bound (fun i => (x i:UnitAddCircle))
  simpa only [actual,dif_pos hr,WilsonOriginalSupportedMixedJets.field,ContinuousMap.coe_mk,
    realValue (WilsonOriginalSupportedMixedJets.support dir (held r) j) left right hx] using pt

end YM.Integration.WilsonOriginalLocalizedMixedSalary
