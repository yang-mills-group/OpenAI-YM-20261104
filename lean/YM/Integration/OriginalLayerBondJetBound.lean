import YM.Integration.NativeNormalizedBondTest
import YM.Integration.NativeRestoredLayerJets
import YM.Integration.NativeAnchoredTensorMarginal

/-! The original layer list evaluated on the actual normalized bond field.
A repeated physical coordinate is one summand of the existing fixed-port
tensor bound. The full nonlinear payload and every atom, root and list
occurrence remain. Order zero is centered exactly. The constant is chosen
before the Run, period, original layers and positive width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalLayerBondJetBound

open Function Filter Set Metric Lattice Wilson RG Precision Exterior PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Comparison.RG02.Assembly NativeNormalizedBondTest NativeAtomTensorLocality
open scoped Topology BigOperators ContDiff Classical

/-- The actual bond field is one native physical field coordinate. -/
theorem bond_coordinate (G : Gauge) (s : Side) (k : G.ColorIndex) :
    bondField G s k = coordinate (anchor s, k) := by
  funext e
  by_cases he : e = anchor s
  · simp only [bondField, scalarBond, coordinate, if_pos he, one_smul, colorUnit]
  · simp only [bondField, scalarBond, coordinate, if_neg he, zero_smul]

private theorem zero_direction {G : Gauge} {s : Side}
    (f : fieldDir G s 1 → ℝ) (d : ℕ) : jet f (d + 1) 0 = 0 := by
  unfold jet
  rw [(iteratedFDeriv ℝ (d + 1) f 0).map_coord_zero (0 : Fin (d + 1)) rfl,
    smul_zero]

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

variable {G : Gauge} {s : Side} {layers : List (Piece G s)} {p : BudgetPoint}
    {order rankCap : ℕ} {width budget : ℝ}

private theorem budget_nonneg
    (H : GradedVacuumLayers layers p order rankCap width budget) : 0 ≤ budget := by
  have hcost : 0 ≤ (layers.map H.packets.pieceCost).sum := by
    apply List.sum_nonneg
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact Extra.Iteration.Cost.nonneg (H.packets.exponential a ha 0)
  exact hcost.trans H.packets.total

private theorem one_layer
    (H : GradedVacuumLayers layers p order rankCap width budget)
    (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers) (d : ℕ) (k : G.ColorIndex) :
    ‖jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
        (d + 1) (bondField G s k) -
      jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
        (d + 1) 0‖ ≤
    ∑ z : Fin (d + 1) → Index G s, if z 0 = (anchor s, k) then
      ∑' i : ℕ, ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1) z‖
      else 0 := by
  let i0 : Index G s := (anchor s, k)
  let q0 : Fin (d + 1) → Index G s := fun _ => i0
  let f (i : ℕ) := tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1) q0
  have hs : Summable (fun i : ℕ => ‖f i‖) :=
    (NativeAnchoredAtomBudget.rooted_tensor H hw a ha (d + 1) q0 0).2.1
  have hj :
      jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
        (d + 1) (bondField G s k) = ∑' i : ℕ, f i := by
    refine (NativeRestoredLayerJets.payload_jet H hw a ha (d + 1)
      (bondField G s k)).trans ?_
    apply tsum_congr
    intro i
    simp only [f, q0, i0, jet, tensor, bond_coordinate, smul_eq_mul]
  rw [zero_direction, sub_zero, hj]
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  let F (z : Fin (d + 1) → Index G s) :=
    ∑' i : ℕ, ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1) z‖
  have hF (z : Fin (d + 1) → Index G s) : 0 ≤ F z :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hsingle := Finset.single_le_sum (s := Finset.univ)
    (f := fun z : Fin (d + 1) → Index G s => if z 0 = i0 then F z else 0)
    (fun z _ => by
      split_ifs
      · exact hF z
      · exact le_refl 0)
    (Finset.mem_univ q0)
  simpa only [F, f, q0, i0, ite_true] using hsingle

/-- The full centered layer jet has the original reciprocal-width polynomial bill. -/
theorem layers_bound (G : Gauge) (rankCap n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {s : Side} {layers : List (Piece G s)} {p : BudgetPoint}
      {order : ℕ} {width budget : ℝ}
      (_H : GradedVacuumLayers layers p order rankCap width budget),
      0 < width → ∀ k : G.ColorIndex,
      (layers.map fun a =>
        ‖jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
            n (bondField G s k) -
          jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
            n 0‖).sum ≤ budget * C * (1 + width⁻¹) ^ (7 * n) := by
  cases n with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro s layers p order width budget H _hw _k
      simpa using budget_nonneg H
  | succ d =>
      obtain ⟨C, hC, h⟩ := NativeAnchoredTensorMarginal.total_marginal G rankCap d
      refine ⟨C, hC, ?_⟩
      intro s layers p order width budget H hw k
      have hl := list_sum_le layers
        (fun a =>
          ‖jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
              (d + 1) (bondField G s k) -
            jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
              (d + 1) 0‖)
        (fun a => ∑ z : Fin (d + 1) → Index G s, if z 0 = (anchor s, k) then
          ∑' i : ℕ, ‖tensor (H.packets.atom a i) (a.packet.labels i).site (d + 1) z‖
          else 0)
        (fun a ha => one_layer H hw a ha d k)
      exact hl.trans (h H hw 0 (anchor s, k))

/-- The same constant applies to every original Run and actual period. -/
theorem actual_layers_bound (G : Gauge) (rankCap n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : Run G) (hG : G.Simple) (m period : ℕ)
      {layers : List (Piece G (R.family.side m period))} {p : BudgetPoint}
      {order : ℕ} {width budget : ℝ}
      (_H : GradedVacuumLayers layers p order rankCap width budget),
      0 < width →
      (layers.map fun a =>
        ‖jet (fun B : fieldDir G (R.family.side m period) 1 =>
            unmaskedPayload a.packet (represent B)) n (actualField R hG m period) -
          jet (fun B : fieldDir G (R.family.side m period) 1 =>
            unmaskedPayload a.packet (represent B)) n 0‖).sum ≤
        budget * C * (1 + width⁻¹) ^ (7 * n) := by
  obtain ⟨C, hC, h⟩ := layers_bound G rankCap n
  refine ⟨C, hC, ?_⟩
  intro R hG m period layers p order width budget H hw
  simpa only [actualField, normalizedField] using h H hw (colorIndex G hG)

end YM.Integration.OriginalLayerBondJetBound
end
