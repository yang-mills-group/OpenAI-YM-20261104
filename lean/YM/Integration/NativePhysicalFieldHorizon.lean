import YM.Integration.NativePhysicalFieldMatrix
import YM.RG11Proof.Horizon.Quotient

/-! Compatibility of the original named physical field matrix under a
change of the finite field horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativePhysicalFieldHorizon

open Function Labels FVA2 FVA2.Verne Pert.Position PositionX
open FormalOPE.RG10.Position RG11.Jets RG11.Horizon NativePhysicalFieldMatrix
open scoped BigOperators Classical

variable {G : Gauge} {d H : ℕ}

def includeDeck (F : Frames G) (h : d ≤ H) : Deck F d ↪ Deck F H :=
  ⟨Deck.climb F h, Deck.climb_inj F h⟩

theorem coherent (F : Frames G) (h : d ≤ H) :
    Coherent (includeDeck F h) (allowance F d) (allowance F H) := by
  constructor
  · intro a i j hj
    have out : d < Deck.price F H j := lt_of_not_ge fun hl => hj (Deck.of_price F h hl)
    exact (a.property : Matrix.BlockTriangular a.val (OrderDual.toDual ∘ Deck.price F H))
      ((Deck.price_bound F d i).trans_lt out)
  · intro a i j hij
    exact (a.property : Matrix.BlockTriangular a.val (OrderDual.toDual ∘ Deck.price F H))
      (i := includeDeck F h i) (j := includeDeck F h j) hij

private theorem actual_inclusion (V : Warehouse G) (h : d ≤ H) :
    higher V.F h = PositionX.up V.F h := by
  apply LinearMap.ext
  intro v
  apply Extra.FD.writes_inj V.F H
  rw [writes_higher, Fountain.common_L V, Fountain.common_L V]
  exact (Maxwell.Free.address_rise V.F _ h v).symm

private theorem ticket (V : Warehouse G) (p : Hop V.F) (h : d ≤ H) (k : ℕ) :
    take (includeDeck V.F h) (YM.FVAAlt2.First.Tent.ticket (p.Z.wire H k)) =
      YM.FVAAlt2.First.Tent.ticket (p.Z.wire d k) := by
  ext a b
  have lift_basis (u : Deck V.F d) : higher V.F h ((deck V.F d) u) =
      (deck V.F H) (includeDeck V.F h u) := cabin V.F h u
  change (((deck V.F H).equivFun ((p.Z.wire H k).val
      ((deck V.F H) (includeDeck V.F h a)))) (includeDeck V.F h b)).re =
    (((deck V.F d).equivFun ((p.Z.wire d k).val ((deck V.F d) a))) b).re
  rw [← lift_basis, actual_inclusion V h, ← PositionX.zoomL_eq,
    show PositionX.zoomL V.F h (p.Z.wire H k) = p.Z.wire d k from congrFun (p.Z.proceeds h) k,
    ← actual_inclusion V h]
  apply congrArg Complex.re
  generalize (p.Z.wire d k).val ((deck V.F d) a) = v
  conv_lhs => rw [← (deck V.F d).sum_equivFun v, map_sum, map_sum]
  simp_rw [Finset.sum_apply, map_smul, lift_basis, Pi.smul_apply, Module.Basis.equivFun_self]
  simp

private theorem physical_piece {F : Frames G} (p : Hop F) (d k : ℕ) :
    piece k (field p d) = (if k = 0 then 1 else 0) + Matrix.of (YM.FVAAlt2.First.Tent.ticket (p.Z.wire d k)) := by
  ext i j
  rw [piece_apply, field, PowerSeries.coeff_mk, Matrix.add_apply]
  by_cases hk : k = 0 <;> simp [hk]

theorem fields (V : Warehouse G) (p : Hop V.F) (h : d ≤ H) :
    take (includeDeck V.F h) (field p H) = field p d := by
  apply extPiece
  intro k
  rw [← take_piece, physical_piece, physical_piece]
  change take (includeDeck V.F h) (if k = 0 then 1 else 0) +
    take (includeDeck V.F h) (YM.FVAAlt2.First.Tent.ticket (p.Z.wire H k)) = _
  rw [ticket V p h]
  by_cases hk : k = 0
  · simp only [if_pos hk, take_one]
    rfl
  · simp only [if_neg hk]
    rfl

theorem physical (V : Warehouse G) (p : Hop V.F) (h : d ≤ H) :
    restrict (includeDeck V.F h) (scheme p H) = scheme p d :=
  Change.ext rfl (fields V p h)

theorem inverse (V : Warehouse G) (p : Hop V.F) (h : d ≤ H) :
    restrict (includeDeck V.F h) (Change.undo (scheme p H) (good p H)) =
      Change.undo (scheme p d) (good p d) := by
  rw [Coherent.sym_inverse (includeDeck V.F h) (coherent V.F h) (good p H)]
  simp only [physical V p h]

theorem compose {F : Frames G} (h : d ≤ H) (c b : Change ℝ (Deck F H))
    (hc : Change.Good (allowance F H) c) :
    restrict (includeDeck F h) (Change.compose c b) =
      Change.compose (restrict (includeDeck F h) c) (restrict (includeDeck F h) b) := by
  refine Change.ext rfl ?_
  change take (includeDeck F h) (c.Z * subs c.g b.Z) =
    take (includeDeck F h) c.Z * subs c.g (take (includeDeck F h) b.Z)
  rw [take_mul _ (Coherent.allHeld _ (coherent F h) hc.field), take_subs]

end YM.Integration.NativePhysicalFieldHorizon
end
