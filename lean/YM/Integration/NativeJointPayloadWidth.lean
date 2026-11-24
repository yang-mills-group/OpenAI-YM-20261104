import YM.Integration.NativeJointPayloadTensor

/-! Lower only the analytic atom width. The full original GradedVacuumLayers
receipt stays at sourceWidth, including its original width reserve, supports,
list occurrences and piece costs. No narrowed grading record is constructed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeJointPayloadWidth

open Function Filter Set Metric Lattice Wilson RG Precision Tree Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Push.Uniform NativeJointPayloadTensor
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {c f : Side} {ratio : Ratio c f} (B : Forest ratio)
variable {N : ℕ} {Z sourceWidth mu budget : ℝ}
variable {layers : List (Piece G f)} {p : BudgetPoint} {order rankCap : ℕ}
variable (H : GradedVacuumLayers layers p order rankCap sourceWidth budget)

private theorem root_budget (hle : mu ≤ sourceWidth)
    (a : Piece G f) (ha : a ∈ layers) (o : Site f) :
    SumBudget (fun i : ℕ => if (a.packet.labels i).site = o
      then (H.packets.atom a i).budget mu else 0) (H.packets.pieceCost a) := by
  have hs : SumBudget (fun i : ℕ => if (a.packet.labels i).site = o
      then (H.packets.atom a i).budget sourceWidth else 0) (H.packets.pieceCost a) := by
    simpa only [Atom.budget] using H.packets.exponential a ha o
  apply Extra.Iteration.Cost.mono hs
  · intro i
    by_cases hi : (a.packet.labels i).site = o
    · rw [if_pos hi]
      unfold Atom.budget Atom.magnitude
      positivity
    · simp only [if_neg hi, le_refl]
  · intro i
    by_cases hi : (a.packet.labels i).site = o
    · simp only [if_pos hi, Atom.budget]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_monotone (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))
        (by unfold Atom.magnitude; positivity)
    · simp only [if_neg hi, le_refl]

/-- The original per-root budget pays the complete nonlinear payload Scatter norm. -/
theorem payload_scatter_le (hs : PaintSupply G N Z) (hmu : 0 < mu) (hle : mu ≤ sourceWidth)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    (a : Piece G f) (ha : a ∈ layers) :
    Scatter (address B G) (weaker N (entryWidth N ratio.count mu)) N
      (fun z => unmaskedPayload a.packet (fine G B z)) x
      (H.packets.pieceCost a * atomCost G Z mu N a.rank *
        countCost (entryWidth N ratio.count mu / 2)) := by
  let u (i : ℕ) (z : Positions (Joint B G)) :=
    (H.packets.atom a i).unmasked (fine G B z) (a.packet.labels i).site
  have he : (fun z => unmaskedPayload a.packet (fine G B z)) = (fun z => ∑' i, u i z) := by
    funext z
    exact tsum_congr fun i => H.packets.original_action a ha i (fine G B z)
  rw [he]
  apply rooted_scatter (root := fun i => (a.packet.labels i).site)
    (F := fun i => (H.packets.atom a i).budget mu)
    (width_positive hmu N ratio.count) (H.packets.piece_cost_nonnegative a ha)
    (atomCost_nn hs hmu a.rank)
  · intro i
    unfold Atom.budget Atom.magnitude
    positivity
  · intro o
    exact root_budget H hle a ha o
  · intro i z hz
    exact (atom_joint B hs hmu z hz (H.packets.atom a i) (a.packet.labels i).site).1
  · exact hx
  · intro i
    exact (atom_joint B hs hmu x hx (H.packets.atom a i) (a.packet.labels i).site).2


/-- Every remaining native joint coordinate is summed, with literal factorial normalization. -/
theorem payload_marginal_le (hs : PaintSupply G N Z) (hmu : 0 < mu) (hle : mu ≤ sourceWidth)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    (a : Piece G f) (ha : a ∈ layers) {d : ℕ} (hd : d + 1 ≤ N)
    (j : Fin (d + 1)) (i0 : Joint B G) :
    (∑ q : Fin d → Joint B G,
      ‖(((d + 1).factorial : ℝ)⁻¹) •
        entry (fun z => unmaskedPayload a.packet (fine G B z)) x (Fin.insertNth j i0 q)‖) ≤
      (H.packets.pieceCost a * atomCost G Z mu N a.rank *
        countCost (entryWidth N ratio.count mu / 2)) *
      ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count mu))) ^ d := by
  have hr := width_positive hmu N ratio.count
  have hwk : 0 < weaker N (entryWidth N ratio.count mu) := by unfold weaker; positivity
  exact ScatterAnchoredSum.normalized (payload_scatter_le B H hs hmu hle x hx a ha)
    (town B) hwk
    (mul_nonneg (mul_nonneg (H.packets.piece_cost_nonnegative a ha) (atomCost_nn hs hmu a.rank))
      (count_pos (half_pos hr)).le) hd j i0


private theorem map_sum_bound {α : Type} (s : List α) (F f : α → ℝ) (K : ℝ) :
    (∀ a ∈ s, F a ≤ f a * K) → (s.map F).sum ≤ (s.map f).sum * K := by
  induction s with
  | nil => intro _h; simp
  | cons a s ih =>
    intro h
    exact (add_le_add (h a (List.mem_cons_self ..))
      (ih fun b hb => h b (List.mem_cons_of_mem a hb))).trans_eq (add_mul _ _ _).symm


include H in
/-- The original list budget pays all payload marginals, preserving duplicate rows. -/
theorem layers_marginal_le (hs : PaintSupply G N Z) (hmu : 0 < mu) (hle : mu ≤ sourceWidth)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    {d : ℕ} (hd : d + 1 ≤ N) (j : Fin (d + 1)) (i0 : Joint B G) :
    (layers.map fun a => ∑ q : Fin d → Joint B G,
      ‖(((d + 1).factorial : ℝ)⁻¹) •
        entry (fun z => unmaskedPayload a.packet (fine G B z)) x (Fin.insertNth j i0 q)‖).sum ≤
      budget * (rankPrice G Z mu N rankCap * countCost (entryWidth N ratio.count mu / 2) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count mu))) ^ d) := by
  let K := rankPrice G Z mu N rankCap * countCost (entryWidth N ratio.count mu / 2) *
    ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count mu))) ^ d
  have hr := width_positive hmu N ratio.count
  have hwk : 0 < weaker N (entryWidth N ratio.count mu) := by unfold weaker; positivity
  have hrank : 0 ≤ rankPrice G Z mu N rankCap :=
    Finset.sum_nonneg fun k _ => atomCost_nn hs hmu k
  have hc : 0 ≤ countCost (entryWidth N ratio.count mu / 2) := (count_pos (half_pos hr)).le
  have hd0 : 0 ≤ ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count mu))) ^ d :=
    pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (count_pos hwk).le) d
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hrank hc) hd0
  apply (map_sum_bound layers _ H.packets.pieceCost K ?_).trans
    (mul_le_mul_of_nonneg_right H.packets.total hK)
  intro a ha
  have hcost : atomCost G Z mu N a.rank ≤ rankPrice G Z mu N rankCap :=
    Finset.single_le_sum (fun k _ => atomCost_nn hs hmu k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (H.packets.rank_bounded a ha)))
  calc
    _ ≤ (H.packets.pieceCost a * atomCost G Z mu N a.rank *
          countCost (entryWidth N ratio.count mu / 2)) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count mu))) ^ d :=
      payload_marginal_le B H hs hmu hle x hx a ha hd j i0
    _ ≤ (H.packets.pieceCost a * rankPrice G Z mu N rankCap *
          countCost (entryWidth N ratio.count mu / 2)) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count mu))) ^ d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcost (H.packets.piece_cost_nonnegative a ha)) hc) hd0
    _ = _ := by dsimp [K]; ring


end YM.Integration.NativeJointPayloadWidth
end
