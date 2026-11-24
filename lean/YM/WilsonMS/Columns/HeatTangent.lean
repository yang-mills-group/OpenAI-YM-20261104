import YM.WilsonMS.Columns.RankProp
/-!
# Highest engineering jet survives every finite-flow t
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.StrictRank
open MS Function Filter Finset Set MeasureTheory Metric
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Real Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Cylinder Lab Draft Wind Wind.Leading Menus Lifting
  LoopRank
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {q v : ℤ} {p : Team} {B P : Dec G} {F : Actor G} (x t : ℝ)
  {u V w : List (Lane4 G)} {h U i j k : ℕ}

private lemma derivative_rule {F H : Wind.Flow G} (h : TouchF F) (hp : TouchF H)
    (hx : ∀ t, Zip F (H t) t) (v : List (Lane4 G)) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => torch j (F t) v) (torch j (H t) v) t := by
  let W := ray v
  let Q : ℝ × ℝ → ℂ := fun p : ℝ × ℝ => H p.1 (sail W p.2)
  have hQ : ContDiff ℝ ∞ Q := jointWay hp W
  have hv (s : ℝ) : fieldVal (F s) W = fieldVal (F 0) W + fun x : ℝ => desk Q (s, x) := by
    nth_rw 1 [term_account h hp hx]
    rfl
  have hF := h.routine W 0
  have ht (s : ℝ) : ContDiff ℝ ∞ (fun x : ℝ => desk Q (s, x)) := (park hQ).comp (by fun_prop)
  have he :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ j (fieldVal (F t) W) 0)
      (iteratedFDeriv ℝ j (fieldVal (H t) W) 0) t := by
    rw [show
        (fun t : ℝ => iteratedFDeriv ℝ j (fieldVal (F t) W) 0) =
          (fun t => iteratedFDeriv ℝ j (fieldVal (F 0) W + fun x : ℝ => desk Q (t, x)) 0)
        from funext (fun i => congr_arg (fun g => iteratedFDeriv ℝ j g 0) (hv i))]
    simp_rw [iteratedFDeriv_add
        ((show ContDiff ℝ ∞ (fieldVal (F 0) W) from hF).of_le (by exact_mod_cast le_top))
        ((ht _).of_le (by exact_mod_cast le_top)),
      Pi.add_apply]
    exact (deskD_iter hQ j t 0).const_add _
  let L : (Tensor.T ℝ ℂ j) →L[ℝ] ℂ :=
    ((j.factorial : ℝ)⁻¹) • ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℂ (fun _ => 1)
  exact L.hasFDerivAt.comp_hasDerivAt _ he

lemma running_w (hp : Valid p) (hG : G.Simple) (hB : PC G p B) (hm : PM F B P q)
    (hU : ∀ i, pays (i + k) (F x i).val) {n : ℕ} (ht : ∀ n', riseH (run (F x n')) (n' + k) v false)
    (w : List (Lane4 G)) (hw : w.length = n + k) (hz : fieldDim wfield w + j ≤ v) :
    torch j (P n x t) w = torch j (run (F x n)) w := by
  induction n using Nat.strong_induction_on generalizing w j t with
  | h n ih =>
    let T := P n x
    let f := run (F x n)
    let R := Wind.path 1 n 0 B P x
    have he : Sat f T R := hm.recu n x
    have hT : TouchF T := ((hm.owes n).stay x).joint
    have hP (i t) : pays (i + k) (P i x t) := Pm_b x hm hB hp hU i t
    have htR : TouchF R :=
      ((path_c 1 n 0 B P (fun _ _ => hB.owes _) (fun _ _ => hm.owes _)).stay x).joint
    let X := Wiref G T
    have hx : TouchF X := lapid_touch hT (main_f G)
    have hC : TouchF (X + R) := TouchF.add hx htR
    have hE {t : ℝ} (w : List (Lane4 G)) (hw : w.length = n + k) : X t w = 0 := by
      change orbit (Cpu G t) μzone (P n x t) w = 0
      rw [finite_cc μzone (period0 μzone cour0 (main_f _) hT)]
      unfold Ccy
      have hu (q : QP) : trc (Cpu G t) q (P n x t) w = 0 := by
        rw [at_trc]
        refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
        rw [hP n t _ ?_, mul_zero]
        intro hy
        have he := hy.smaller
        simp only [hw, List.length_cons] at he
        omega
      change (∫ q : QP, trc (Cpu G t) q (P n x t) w ∂μzone) = _
      simp_rw [hu]
      simp
    have hs (r : ℝ) : HasDerivAt (fun t => torch j (T t) w) 0 r := by
      have hh := derivative_rule hT hC he.2 w j r
      have hX : fieldVal (X r) (ray w) = 0 := funext fun i => hE _ (by rw [sail_len, ray_len, hw])
      suffices hq : Rest (fieldVal ((X + R) r) (ray w)) (v - fieldDim wfield w) 0 by
        refine
          hh.congr_deriv
            (by
              rw [torch_at]
              change reading j (fieldVal _ _) = _
              rw [hq.home j (by omega)]
              simp)
      have hr (i : ℕ) (hi : i ∈ Domain.paths n 0) :
        Rest (fieldVal (treeP G (B (n - i) x) (P i x) r) (ray w)) (v - fieldDim wfield w) 0 := by
        have hp' : i < n := (path_in hi).2
        refine
          post_m r (i := (n - i) + 2) (j := i + k) (Pc_b x hB hp (n - i) r) (hP i r)
            (BulkP x r hB hG _ (by omega)) ?_ (by omega) hw
        intro v' hv' hC
        obtain ⟨d, hd⟩ := ht i v' hv' hC
        refine ⟨d, ((hm.owes i).stay x).joint.routine _ _, hd.bottom, fun j hj => ?_⟩
        rw [← hd.home j hj]
        exact ih i hp' r v' hv' (by omega)
      change Rest (fieldVal (X r + R r) (ray w)) _ _
      have hR : Rest (fieldVal (R r) (ray w)) (v - fieldDim wfield w) 0 := by
        let K (i : ℕ) (w' : ℝ) := fieldVal (treeP G (B (n - i) x) (P i x) r) (ray w) w'
        have hb := Rest.sum (x := fun _ : ℕ => 0) (f := K) (Domain.paths n 0) (h := hr)
        simp only [Finset.sum_const_zero] at hb
        rw [show fieldVal (R r) (ray w) = _ from ?_]
        exact hb
        unfold fieldVal R Wind.path
        funext z
        simp only [one_smul, Finset.sum_apply]
        rfl
      rw [show fieldVal _ _ = fieldVal (R r) (ray w) from ?_]
      exact hR
      change fieldVal (X r) (ray w) + fieldVal (R r) (ray w) = _
      rw [hX, zero_add]
    rw [show P n x t = T t from rfl, constancy hs t, he.1]
end YM.WilsonMS.StrictRank
