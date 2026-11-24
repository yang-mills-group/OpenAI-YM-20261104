import YM.Integration.WilsonOriginalInteriorMultiplier
import YM.Integration.WilsonOriginalLocalizedMixedSalary

/-! All ordered point jets of the unweighted original comparison on a
cleared compact subbox. The window and its reciprocal are fixed geometrically. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalInteriorShapeValues
open Filter Set Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb UnitAddTorus
open WilsonOriginalSupportedBoxChart (Space)
open WilsonOriginalSpatialProductRule (word Regular)
open WilsonOriginalInteriorMultiplier (Priced)
open WilsonOriginalInteriorValues (weight)
open WilsonOriginalCompactlyFiledResidual (raw)
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalTestedFourierBank (Prices)
open scoped ContDiff Topology BigOperators Classical

theorem original {G : Gauge} {u : ℝ → ℝ} (simple : G.Simple) (clock : Coupling G u)
    {d : ℕ} (l h : Space (d+1)) (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1)
    (f : ℝ → Space (d+1) → ℂ) (a : ℕ → Space (d+1) → ℂ)
    (sf : ∀ᶠ r in trail, ∀ x : Space (d+1), (∀ i, x i ∈ Icc (0:ℝ) 1) → ContDiffAt ℝ ∞ (f r) x)
    (sa : ∀ k x, (∀ i, x i ∈ Icc (0:ℝ) 1) → ContDiffAt ℝ ∞ (a k) x)
    (price : Prices u (fun r v => mFourierCoeff (localize 0 l h (f r)) v)
      (fun k v => mFourierCoeff (localize 0 l h (a k)) v))
    (K : Set (Space (d+1))) (compact : IsCompact K) (inside : ∀ x ∈ K, ∀ i, x i ∈ Ioo (l i) (h i))
    (p : ℕ) (s : List (Fin (d+1))) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K,
      ‖word s (fun y => f r y-∑ k : Fin (p+1), (u r:ℂ)^k.val*a k.val y) x‖ ≤ ε*u r^p := by
  let O := univ.pi (fun i => Ioo (l i) (h i))
  have room : IsOpen O := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have cover : K ⊆ O := fun x hx i _ => inside x hx i
  have cube (x : Space (d+1)) (hx : x ∈ O) (i : Fin (d+1)) : x i ∈ Icc (0:ℝ) 1 :=
    ⟨(left i).le.trans (hx i (mem_univ i)).1.le,(hx i (mem_univ i)).2.le.trans (right i).le⟩
  have fixed : ContDiff ℝ ∞ (weight l h) :=
    contDiff_prod (fun i _ => (WilsonOriginalFiledBoxWindow.smooth _ _).comp (contDiff_apply ℝ ℝ i))
  have nz (x : Space (d+1)) (hx : x ∈ O) : weight l h x ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [← norm_pos_iff,WilsonOriginalFiledBoxWindow.norm_window]
    exact mul_pos (expNegInvGlue.pos_of_pos (sub_pos.mpr (hx i (mem_univ i)).1))
      (expNegInvGlue.pos_of_pos (sub_pos.mpr (hx i (mem_univ i)).2))
  let R := fun r => raw l h (f r) a (u r) p
  have reg : ∀ᶠ r in trail, Regular O (R r) := by
    filter_upwards [sf] with r field x hx
    apply fixed.contDiffAt.mul
    apply (field x (cube x hx)).sub
    exact ContDiffAt.sum (fun k _ => contDiffAt_const.mul (sa k.val x (cube x hx)))
  have marked (t : List (Fin (d+1))) : Priced K (fun r => u r^p) (fun r => word t (R r)) := by
    intro tol pos
    let dir := fun j : ℕ => if hj : j < t.length then t[j] else 0
    have printed : List.ofFn (fun k : Fin t.length => dir k.val) = t := by
      simpa only [dir,dif_pos,Fin.isLt] using (show List.ofFn (fun k : Fin t.length => t[k.val]) = t from List.ofFn_getElem)
    have w := WilsonOriginalLocalizedMixedSalary.original simple clock l h left right f a sf sa price p t.length dir pos
    filter_upwards [w] with r got x hx
    rw [← printed,WilsonOriginalSpatialProductRule.sampled]
    exact got x (cube x (cover hx))
  have priced := WilsonOriginalInteriorMultiplier.original s compact cover room (fun r => u r^p)
    (fun x => (weight l h x)⁻¹) (fun x hx => fixed.contDiffAt.inv (nz x hx)) R reg marked ε eps
  filter_upwards [priced] with r paid x hx
  have id : EqOn (fun y => (weight l h y)⁻¹*R r y)
      (fun y => f r y-∑ k : Fin (p+1), (u r:ℂ)^k.val*a k.val y) O := by
    intro y hy
    dsimp only
    rw [show R r y = weight l h y*(f r y-∑ k : Fin (p+1), (u r:ℂ)^k.val*a k.val y) from rfl,
      inv_mul_cancel_left₀ (nz y hy)]
  rw [← WilsonOriginalSpatialProductRule.germ s O room id (cover hx)]
  exact paid x hx

end YM.Integration.WilsonOriginalInteriorShapeValues
