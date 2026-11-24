import YM.Integration.NativeAtomTensorLocality
import YM.Extra.ITERATION_NO_LOSS.Sums

/-! Absolute one-port bounds for the original ordered atom tensors.
Every root, original atom and free physical coordinate is summed. The
native lattice decay count and the fixed axis/color multiplicity replace
any lattice-volume count. Every port may be the distinguished one; no
symmetrization or factorial cancellation is performed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeAnchoredAtomBudget

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Comparison.RG02.Assembly Push.Uniform NativeAtomTensorLocality
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {s : Side}

def coordinateCount (G : Gauge) : ℕ := Fintype.card (TypeFace 1 × G.ColorIndex)

/-- The coordinate multiplicity is fixed by the gauge and the physical axes. -/
theorem coordinate_multiplicity :
    Multiplicity (location (G := G) (s := s)) (coordinateCount G) := by
  let t (i : Index G s) : TypeFace 1 × G.ColorIndex := (i.1.2, i.2)
  intro x
  have hi : Set.InjOn t ↑(Finset.univ.filter fun i : Index G s => location i = x) := by
    intro i hi j hj he
    have hl : i.1.1 = j.1.1 := (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    have haxis : i.1.2 = j.1.2 :=
      congrArg (fun z : TypeFace 1 × G.ColorIndex => z.1) he
    have hcolor : i.2 = j.2 :=
      congrArg (fun z : TypeFace 1 × G.ColorIndex => z.2) he
    exact Prod.ext (Prod.ext hl haxis) hcolor
  have h := Finset.card_le_card_of_injOn t (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) hi
  simpa only [coordinateCount, Finset.card_univ] using h

private theorem rate_pos {width : ℝ} (hw : 0 < width) (d : ℕ) :
    0 < rate d width := by unfold rate; positivity

private theorem factor_nonneg {width : ℝ} (hw : 0 < width) (d cap : ℕ) :
    0 ≤ NativeRestoredJetBudget.factor G cap d (width / 2) := by
  unfold NativeRestoredJetBudget.factor
  positivity

private theorem weighted_budget {F : ℕ → ℝ} (root : ℕ → Site s) {C : ℝ}
    (hF : ∀ i, 0 ≤ F i)
    (h : ∀ o, SumBudget (fun i => if root i = o then F i else 0) C)
    (w : Site s → ℝ) (hw : ∀ o, 0 ≤ w o) :
    SumBudget (fun i => F i * w (root i)) (C * ∑ o, w o) := by
  let f (o : Site s) (i : ℕ) := (if root i = o then F i else 0) * w o
  have hf (o : Site s) : SumBudget (f o) (C * w o) := Extra.Iteration.Cost.scale' (h o) (w o) (hw o)
  have he : (fun i => F i * w (root i)) = (fun i => ∑ o : Site s, f o i) := by
    funext i
    simp [f]
  have hs : Summable (fun i => ∑ o : Site s, f o i) :=
    summable_sum (s := Finset.univ) (fun o _ => (hf o).2.1)
  refine ⟨fun i => mul_nonneg (hF i) (hw (root i)), he.symm ▸ hs, ?_⟩
  rw [he, Summable.tsum_finsetSum (fun o _ => (hf o).2.1)]
  exact (Finset.sum_le_sum (fun o _ => (hf o).2.2)).trans_eq (Finset.mul_sum ..).symm

private theorem list_sum_le {ι : Type*} (l : List ι) (f g : ι → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  revert h
  induction l with
  | nil => intro _h; simp only [List.map_nil, List.sum_nil, le_refl]
  | cons a l ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (List.mem_cons_self ..))
        (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem list_sum_mul {ι : Type*} (l : List ι) (f : ι → ℝ) (R : ℝ) :
    (l.map fun a => f a * R).sum = (l.map f).sum * R := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, zero_mul]
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, add_mul]

variable {layers : List (Piece G s)} {p : BudgetPoint}
    {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)

/-- Summation over all original roots is paid before summing the free coordinates. -/
theorem rooted_tensor (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers)
    (d : ℕ) (q : Fin d → Index G s) (j : Fin d) :
    SumBudget (fun i : ℕ => ‖tensor (H.packets.atom a i) (a.packet.labels i).site d q‖)
      ((H.packets.pieceCost a * countCost (rate d width / 2) *
        NativeRestoredJetBudget.factor G rankCap d (width / 2)) *
          Real.exp (-weaker d (rate d width) * spanSites location (location (q j)) q)) := by
  let F (i : ℕ) := (H.packets.atom a i).budget width
  let root (i : ℕ) := (a.packet.labels i).site
  let E := Real.exp (-weaker d (rate d width) * spanSites location (location (q j)) q)
  let K := NativeRestoredJetBudget.factor G rankCap d (width / 2)
  have hr := rate_pos hw d
  have hK : 0 ≤ K := factor_nonneg hw d rankCap
  have hC : 0 ≤ H.packets.pieceCost a :=
    Extra.Iteration.Cost.nonneg (H.packets.exponential a ha (location (q j)))
  have hF (i : ℕ) : 0 ≤ F i := by unfold F Atom.budget Atom.magnitude; positivity
  have hf (o : Site s) : SumBudget (fun i => if root i = o then F i else 0) (H.packets.pieceCost a) := by
    simpa only [root, F, Atom.budget] using H.packets.exponential a ha o
  have hW := weighted_budget root hF hf
    (fun o => Decay (rate d width / 2) (location (q j)) o)
    (fun o => (decay_pos ..).le)
  have hW' : SumBudget (fun i => F i * Decay (rate d width / 2) (location (q j)) (root i))
      (H.packets.pieceCost a * countCost (rate d width / 2)) :=
    Extra.Iteration.Cost.enlarge hW
      (mul_le_mul_of_nonneg_left (decay_count (half_pos hr) (location (q j))) hC)
  have hpay := Extra.Iteration.Cost.scale' hW' (K * E) (by positivity)
  have hm : SumBudget
      (fun i : ℕ => ‖tensor (H.packets.atom a i) (root i) d q‖)
      ((H.packets.pieceCost a * countCost (rate d width / 2)) * (K * E)) := by
    apply Extra.Iteration.Cost.mono hpay (fun _ => norm_nonneg _)
    intro i
    calc
      _ ≤ F i * K * Real.exp (-rate d width * spanSites location (root i) q) :=
        tensor_decay (H.packets.atom a i) (root i) hw d rankCap
          (H.packets.rank_bounded a ha) q
      _ ≤ F i * K * (Decay (rate d width / 2) (location (q j)) (root i) * E) :=
        mul_le_mul_of_nonneg_left
          (price_relative (l := location) (y := root i) (N := d) le_rfl q j hr.le)
          (mul_nonneg (hF i) hK)
      _ = _ := by ring
  exact Extra.Iteration.Cost.enlarge hm (le_of_eq (by dsimp only [K, E]; ring))

/-- The fully displayed fixed-order price; the width and rank cap are unchanged. -/
def portFactor (G : Gauge) (cap d : ℕ) (width : ℝ) : ℝ :=
  countCost (rate (d + 1) width / 2) *
    NativeRestoredJetBudget.factor G cap (d + 1) (width / 2) *
      ((coordinateCount G : ℝ) * countCost (weaker (d + 1) (rate (d + 1) width))) ^ d

private theorem exp_insert (d : ℕ) (j : Fin (d + 1)) (i0 : Index G s)
    (q : Fin d → Index G s) (b : ℝ) :
    Real.exp (-b * spanSites location (location i0) (Fin.insertNth j i0 q)) =
      ∏ t, Decay b (location i0) (location (q t)) := by
  unfold spanSites
  rw [Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, separation_self,
    zero_add, Nat.cast_sum, Finset.mul_sum, Real.exp_sum, Decay]

/-- Full absolute summability, at any chosen port, including the no-free-port case. -/
theorem anchored_budget (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers)
    (d : ℕ) (j : Fin (d + 1)) (i0 : Index G s) :
    SumBudget (fun z : (Fin d → Index G s) × ℕ =>
      ‖tensor (H.packets.atom a z.2) (a.packet.labels z.2).site (d + 1)
        (Fin.insertNth j i0 z.1)‖)
      (H.packets.pieceCost a * portFactor G rankCap d width) := by
  let b := weaker (d + 1) (rate (d + 1) width)
  let C := H.packets.pieceCost a * countCost (rate (d + 1) width / 2) *
    NativeRestoredJetBudget.factor G rankCap (d + 1) (width / 2)
  have hr := rate_pos hw (d + 1)
  have hb : 0 < b := by unfold b weaker; positivity
  have hC : 0 ≤ C := by
    have := Extra.Iteration.Cost.nonneg (H.packets.exponential a ha (location i0))
    have := factor_nonneg (G := G) hw (d + 1) rankCap
    have := (count_pos (half_pos hr)).le
    positivity
  have ht : SumBudget (fun i : Index G s => Decay b (location i0) (location i))
      ((coordinateCount G : ℝ) * countCost b) := by
    refine ⟨fun _ => (decay_pos ..).le, (hasSum_fintype _).summable, ?_⟩
    rw [tsum_fintype]
    exact coordinate_multiplicity.count location hb (location i0)
  have hp := Extra.Iteration.Cost.pi (n := d) (fun _ => ht)
  have hp' : SumBudget (fun q : Fin d → Index G s =>
      C * ∏ t, Decay b (location i0) (location (q t)))
      (C * (((coordinateCount G : ℝ) * countCost b) ^ d)) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Extra.Iteration.Cost.scale hp C hC
  have hi (q : Fin d → Index G s) :
      SumBudget (fun i : ℕ => ‖tensor (H.packets.atom a i) (a.packet.labels i).site
        (d + 1) (Fin.insertNth j i0 q)‖)
        (C * ∏ t, Decay b (location i0) (location (q t))) := by
    simpa only [Fin.insertNth_apply_same, exp_insert, C, b] using
      rooted_tensor H hw a ha (d + 1) (Fin.insertNth j i0 q) j
  have h := Extra.Iteration.Cost.product
    (F := fun z : (Fin d → Index G s) × ℕ =>
      ‖tensor (H.packets.atom a z.2) (a.packet.labels z.2).site (d + 1)
        (Fin.insertNth j i0 z.1)‖) hp' hi
  exact Extra.Iteration.Cost.enlarge h (le_of_eq (by unfold C b portFactor; ring))

/-- This is the requested one-port l1 sum of the original normalized coefficients. -/
theorem anchored_sum (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers)
    (d : ℕ) (j : Fin (d + 1)) (i0 : Index G s) :
    (∑ q : Fin d → Index G s, ∑' i : ℕ,
      ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1)
        (Fin.insertNth j i0 q)‖) ≤ H.packets.pieceCost a * portFactor G rankCap d width := by
  have h := anchored_budget H hw a ha d j i0
  have he := h.2.2
  rw [h.2.1.tsum_prod, tsum_fintype] at he
  exact he

/-- Every finite-list occurrence is charged to the same original total budget. -/
theorem total_anchored (hw : 0 < width) (d : ℕ) (j : Fin (d + 1)) (i0 : Index G s) :
    (layers.map fun a => ∑ q : Fin d → Index G s, ∑' i : ℕ,
      ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1)
        (Fin.insertNth j i0 q)‖).sum ≤ budget * portFactor G rankCap d width := by
  have hr := rate_pos hw (d + 1)
  have hb : 0 < weaker (d + 1) (rate (d + 1) width) := by unfold weaker; positivity
  have hP : 0 ≤ portFactor G rankCap d width := by
    have := (count_pos (half_pos hr)).le
    have := (count_pos hb).le
    have := factor_nonneg (G := G) hw (d + 1) rankCap
    unfold portFactor
    positivity
  refine (list_sum_le layers _ (fun a => H.packets.pieceCost a * portFactor G rankCap d width)
    (fun a ha => anchored_sum H hw a ha d j i0)).trans ?_
  rw [list_sum_mul]
  exact mul_le_mul_of_nonneg_right H.packets.total hP

end YM.Integration.NativeAnchoredAtomBudget
end
