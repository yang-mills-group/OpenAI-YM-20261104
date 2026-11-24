import YM.Integration.QLocalGradedVacuumLayers
import YM.Integration.ScatterAnchoredSum
import YM.Push.STATIONARY_UNIFORM.Entries

/-! The full original payload on the native nonlinear coarse/fine chart.
The infinite atom sum keeps its original roots and per-root exponential
budget. Spatial decay pays the root sum; Array.town pays all remaining
coordinate sums. Neither step introduces a torus-volume factor. The finite
rank sum below is explicit, and no coupling power is absorbed into it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeJointPayloadTensor

open Function Filter Set Metric Lattice Wilson RG Precision Tree Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Push.Uniform
open scoped Topology BigOperators ContDiff Classical

section RootSum
variable {s : Side} {α ι : Type} [Fintype ι]

private theorem weighted_budget {F : α → ℝ} (root : α → Site s) {C : ℝ}
    (hF : ∀ i, 0 ≤ F i)
    (h : ∀ o, SumBudget (fun i => if root i = o then F i else 0) C)
    (w : Site s → ℝ) (hw : ∀ o, 0 ≤ w o) :
    SumBudget (fun i => F i * w (root i)) (C * ∑ o, w o) := by
  let f (o : Site s) (i : α) := (if root i = o then F i else 0) * w o
  have hf (o : Site s) : SumBudget (f o) (C * w o) :=
    Extra.Iteration.Cost.scale' (h o) (w o) (hw o)
  have he : (fun i => F i * w (root i)) = (fun i => ∑ o, f o i) := by
    funext i
    simp [f]
  have hs : Summable (fun i => ∑ o, f o i) :=
    summable_sum (s := Finset.univ) (fun o _ => (hf o).2.1)
  refine ⟨fun i => mul_nonneg (hF i) (hw (root i)), he.symm ▸ hs, ?_⟩
  rw [he, Summable.tsum_finsetSum (fun o _ => (hf o).2.1)]
  exact (Finset.sum_le_sum fun o _ => (hf o).2.2).trans_eq (Finset.mul_sum ..).symm

/-- Varying-root infinite sums retain a uniform spatial Scatter bound. -/
theorem rooted_scatter {l : ι → Site s} {root : α → Site s}
    {rate C M : ℝ} {N : ℕ} {u : α → Positions ι → ℝ} {F : α → ℝ}
    {x : Positions ι} (hr : 0 < rate) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hF : ∀ i, 0 ≤ F i)
    (hroot : ∀ o, SumBudget (fun i => if root i = o then F i else 0) C)
    (hu : ∀ i z, z ∈ ball 0 1 → Allows N (u i) z (F i * M))
    (hx : x ∈ ball 0 1)
    (hb : ∀ i, Beacon l rate N (u i) (root i) x (F i * M)) :
    Scatter l (weaker N rate) N (fun z => ∑' i, u i z) x
      (C * M * countCost (rate / 2)) := by
  have hsum : Summable F := by
    have h := (weighted_budget root hF hroot (fun _ => 1) (fun _ => zero_le_one)).2.1
    simpa only [mul_one] using h
  have hP : Summable (fun i => F i * M) := hsum.mul_right M
  intro k hk q j
  have hD : Summable (fun i => iteratedFDeriv ℝ k (u i) x) :=
    .of_norm_bounded hP (fun i => (hu i x hx).norm_le k hk)
  unfold entry
  rw [iterated_at_sum isOpen_ball (convex_ball (0 : Positions ι) 1).isPreconnected
    hP hu hx k hk, ContinuousMultilinearMap.tsum_eval hD]
  let A := l (q j)
  let E := Real.exp (-(weaker N rate) * spanSites l A q)
  let w (o : Site s) := Decay (rate / 2) A o
  have hw := weighted_budget root hF hroot w (fun o => (decay_pos ..).le)
  have hcount : SumBudget (fun i => F i * w (root i)) (C * countCost (rate / 2)) :=
    Extra.Iteration.Cost.enlarge hw
      (mul_le_mul_of_nonneg_left (decay_count (half_pos hr) A) hC)
  have hQ := Extra.Iteration.Cost.scale' hcount (M * E)
    (mul_nonneg hM (Real.exp_pos _).le)
  have he (i : α) : ‖entry (u i) x q‖ ≤ (F i * w (root i)) * (M * E) := by
    calc
      _ ≤ (F i * M) * Real.exp (-rate * spanSites l (root i) q) := hb i k hk q
      _ ≤ (F i * M) * (w (root i) * E) :=
        mul_le_mul_of_nonneg_left (price_relative hk q j hr.le) (mul_nonneg (hF i) hM)
      _ = _ := by ring
  have hnorm := Extra.Iteration.Cost.mono hQ (fun i => norm_nonneg (entry (u i) x q)) he
  calc
    _ ≤ ∑' i, ‖entry (u i) x q‖ := norm_tsum_le_tsum_norm hnorm.2.1
    _ ≤ (C * countCost (rate / 2)) * (M * E) := hnorm.2.2
    _ = _ := by dsimp [E, A]; ring

end RootSum

section Native
variable {G : Gauge} {c f : Side} {ratio : Ratio c f} (B : Forest ratio)
variable {N : ℕ} {Z width : ℝ}

/-- Both analytic and spatial estimates use the full native nonlinear fine field. -/
theorem atom_joint (hs : PaintSupply G N Z) (hw : 0 < width)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    {k : ℕ} (a : Atom G k) (o : Site f) :
    Allows N (fun z => a.unmasked (fine G B z) o) x
        (a.budget width * atomCost G Z width N k) ∧
      Beacon (address B G) (entryWidth N ratio.count width) N
        (fun z => a.unmasked (fine G B z) o) o x
        (a.budget width * atomCost G Z width N k) := by
  have hr := width_positive hw N ratio.count
  obtain ⟨M, hM, hp⟩ := pay_atom B 1 hs x
    (show ‖x‖ ≤ 1 from (show ‖x‖ < 1 by simpa using hx).le) o a hw
  have hu := hM.mono
    ((le_mul_of_one_le_right hM.nonneg (Real.one_le_exp (by positivity))).trans hp)
  have hb : Beacon (address B G) (entryWidth N ratio.count width) N
      (fun z => a.unmasked (signedFine B z 1) o) (affine 1 0 o) x
      (a.budget width * atomCost G Z width N k) := by
    apply Beacon.mono _ hp
    apply Allows.beacon hM (s := Set.univ) _ univ_mem hr.le
    intro u _ v _ he
    unfold Atom.unmasked
    refine congr_arg _ (funext fun b => slot_read B 1 o _ ?_ he)
    have h : (a.leg b).length ≤ a.length :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (a.leg i).length) (Finset.mem_univ b)
    unfold signedCost
    gcongr
  constructor
  · simpa only [signedFine, Lattice.pull_id] using hu
  · simpa [signedFine, affine] using hb

variable {layers : List (Piece G f)} {p : BudgetPoint} {order rankCap : ℕ}
variable {budget : ℝ} (H : GradedVacuumLayers layers p order rankCap width budget)

private theorem atom_budget (a : Piece G f) (ha : a ∈ layers) :
    Summable (fun i : ℕ => (H.packets.atom a i).budget width) := by
  let t (o : Site f) (i : ℕ) :=
    if (a.packet.labels i).site = o then (H.packets.atom a i).budget width else 0
  have ht (o : Site f) : Summable (t o) := by
    simpa only [t, Atom.budget] using (H.packets.exponential a ha o).2.1
  have hsum := summable_sum (s := Finset.univ) (fun o _ => ht o)
  convert hsum using 1
  funext i
  simp [t]

/-- Exact raw ordered entries retain every original varying-root atom. -/
theorem payload_entry (hs : PaintSupply G N Z) (hw : 0 < width)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    (a : Piece G f) (ha : a ∈ layers) (n : ℕ) (hn : n ≤ N)
    (q : Fin n → Joint B G) :
    entry (fun z => unmaskedPayload a.packet (fine G B z)) x q =
      ∑' i : ℕ, entry (fun z =>
        (H.packets.atom a i).unmasked (fine G B z) (a.packet.labels i).site) x q := by
  let u (i : ℕ) (z : Positions (Joint B G)) :=
    (H.packets.atom a i).unmasked (fine G B z) (a.packet.labels i).site
  let C (i : ℕ) := (H.packets.atom a i).budget width * atomCost G Z width N a.rank
  have hC : Summable C := (atom_budget H a ha).mul_right _
  have hu (i : ℕ) (z : Positions (Joint B G)) (hz : z ∈ ball 0 1) : Allows N (u i) z (C i) :=
    (atom_joint B hs hw z hz (H.packets.atom a i) (a.packet.labels i).site).1
  have hD : Summable (fun i => iteratedFDeriv ℝ n (u i) x) :=
    .of_norm_bounded hC (fun i => (hu i x hx).norm_le n hn)
  have he : (fun z => unmaskedPayload a.packet (fine G B z)) = (fun z => ∑' i, u i z) := by
    funext z
    exact tsum_congr fun i => H.packets.original_action a ha i (fine G B z)
  rw [he]
  unfold entry
  rw [iterated_at_sum isOpen_ball (convex_ball (0 : Positions (Joint B G)) 1).isPreconnected
    hC hu hx n hn, ContinuousMultilinearMap.tsum_eval hD]

/-- The original per-root budget pays the complete nonlinear payload Scatter norm. -/
theorem payload_scatter (hs : PaintSupply G N Z) (hw : 0 < width)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    (a : Piece G f) (ha : a ∈ layers) :
    Scatter (address B G) (weaker N (entryWidth N ratio.count width)) N
      (fun z => unmaskedPayload a.packet (fine G B z)) x
      (H.packets.pieceCost a * atomCost G Z width N a.rank *
        countCost (entryWidth N ratio.count width / 2)) := by
  let u (i : ℕ) (z : Positions (Joint B G)) :=
    (H.packets.atom a i).unmasked (fine G B z) (a.packet.labels i).site
  have he : (fun z => unmaskedPayload a.packet (fine G B z)) = (fun z => ∑' i, u i z) := by
    funext z
    exact tsum_congr fun i => H.packets.original_action a ha i (fine G B z)
  rw [he]
  apply rooted_scatter (root := fun i => (a.packet.labels i).site)
    (F := fun i => (H.packets.atom a i).budget width)
    (width_positive hw N ratio.count) (H.packets.piece_cost_nonnegative a ha)
    (atomCost_nn hs hw a.rank)
  · intro i
    unfold Atom.budget Atom.magnitude
    positivity
  · intro o
    simpa only [Atom.budget] using H.packets.exponential a ha o
  · intro i z hz
    exact (atom_joint B hs hw z hz (H.packets.atom a i) (a.packet.labels i).site).1
  · exact hx
  · intro i
    exact (atom_joint B hs hw x hx (H.packets.atom a i) (a.packet.labels i).site).2

/-- Every remaining native joint coordinate is summed, with literal factorial normalization. -/
theorem payload_marginal (hs : PaintSupply G N Z) (hw : 0 < width)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    (a : Piece G f) (ha : a ∈ layers) {d : ℕ} (hd : d + 1 ≤ N)
    (j : Fin (d + 1)) (i0 : Joint B G) :
    (∑ q : Fin d → Joint B G,
      ‖(((d + 1).factorial : ℝ)⁻¹) •
        entry (fun z => unmaskedPayload a.packet (fine G B z)) x (Fin.insertNth j i0 q)‖) ≤
      (H.packets.pieceCost a * atomCost G Z width N a.rank *
        countCost (entryWidth N ratio.count width / 2)) *
      ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d := by
  have hr := width_positive hw N ratio.count
  have hwk : 0 < weaker N (entryWidth N ratio.count width) := by unfold weaker; positivity
  exact ScatterAnchoredSum.normalized (payload_scatter B H hs hw x hx a ha)
    (town B) hwk
    (mul_nonneg (mul_nonneg (H.packets.piece_cost_nonnegative a ha) (atomCost_nn hs hw a.rank))
      (count_pos (half_pos hr)).le) hd j i0

/-- A fixed finite rank sum, without replacing any original payload or credit. -/
def rankPrice (G : Gauge) (Z width : ℝ) (N cap : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (cap + 1), atomCost G Z width N k

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
theorem layers_marginal (hs : PaintSupply G N Z) (hw : 0 < width)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    {d : ℕ} (hd : d + 1 ≤ N) (j : Fin (d + 1)) (i0 : Joint B G) :
    (layers.map fun a => ∑ q : Fin d → Joint B G,
      ‖(((d + 1).factorial : ℝ)⁻¹) •
        entry (fun z => unmaskedPayload a.packet (fine G B z)) x (Fin.insertNth j i0 q)‖).sum ≤
      budget * (rankPrice G Z width N rankCap * countCost (entryWidth N ratio.count width / 2) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d) := by
  let K := rankPrice G Z width N rankCap * countCost (entryWidth N ratio.count width / 2) *
    ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d
  have hr := width_positive hw N ratio.count
  have hwk : 0 < weaker N (entryWidth N ratio.count width) := by unfold weaker; positivity
  have hrank : 0 ≤ rankPrice G Z width N rankCap :=
    Finset.sum_nonneg fun k _ => atomCost_nn hs hw k
  have hc : 0 ≤ countCost (entryWidth N ratio.count width / 2) := (count_pos (half_pos hr)).le
  have hd0 : 0 ≤ ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d :=
    pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (count_pos hwk).le) d
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hrank hc) hd0
  apply (map_sum_bound layers _ H.packets.pieceCost K ?_).trans
    (mul_le_mul_of_nonneg_right H.packets.total hK)
  intro a ha
  have hcost : atomCost G Z width N a.rank ≤ rankPrice G Z width N rankCap :=
    Finset.single_le_sum (fun k _ => atomCost_nn hs hw k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (H.packets.rank_bounded a ha)))
  calc
    _ ≤ (H.packets.pieceCost a * atomCost G Z width N a.rank *
          countCost (entryWidth N ratio.count width / 2)) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d :=
      payload_marginal B H hs hw x hx a ha hd j i0
    _ ≤ (H.packets.pieceCost a * rankPrice G Z width N rankCap *
          countCost (entryWidth N ratio.count width / 2)) *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcost (H.packets.piece_cost_nonnegative a ha)) hc) hd0
    _ = _ := by dsimp [K]; ring

end Native
end YM.Integration.NativeJointPayloadTensor
end
