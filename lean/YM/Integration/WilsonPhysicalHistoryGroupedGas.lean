import YM.Integration.WilsonPhysicalHistoryGroupedHard
import YM.Integration.WilsonPhysicalHistoryGroupedClear
import YM.MergeProof.Figure

/-! The unaltered gas of the enrolled gallery after grouping by both parts
of its actual forced address. All original partners and the original
admissibility predicate appear in the same signed sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedGas
open Finset Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open Extra.Histories Extra.Trajectories QuadraticLocal.Fusion.Attached WilsonPhysicalHistoryGroupedHard
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] [Fintype V] {Z : Census V}
  {G : Gauge} {n : Side} {P : Rep G n} {o : V → Site n} (A : Gallery T I o P Z)
  (w : V → ℝ) (positive : ∀ v, 0 < w v)

omit [Fintype V] in
private theorem entries (t : T) :
    column P o A.K Finset.univ t = A.K.hard t := by
  funext i U
  ext s
  change (if s ∈ (Finset.univ : Finset Z.Mode) then _ else _) = _
  exact if_pos (Finset.mem_univ s)

include positive in
omit [Fintype V] in
theorem gas {a cost : ℝ} (expo : 0 ≤ a) (paid : A.K.Paid w P.p.B a cost)
    (t : T) (U : Config G n) :
    A.gas t U = field (fun box => grouped P o A.K Finset.univ t box U) (flags P.p.threshold U) := by
  have witnessed := (stored P o A.K w positive Finset.univ expo paid t).repair positive U
  rw [entries A t] at witnessed
  let bound := fun i => Poly.price w (A.K.hard t i U)
  have summable : Summable (fun pack : Finset ℕ => ∏ i ∈ pack, bound i) :=
    summable_finsetProd_of_summable_nonneg (fun i => Poly.nonnegative positive _) witnessed.1
  have packetSummable : Summable (fun pack => packet P.activities P.p (A.K.hard t) U pack) := by
    apply (Poly.budgeted positive summable ?_).1
    intro pack
    unfold packet
    split
    · exact Poly.multiple positive _ _
    · simp only [Poly.zero_price]
      exact Finset.prod_nonneg fun i _ => Poly.nonnegative positive _
  have same : Packets.value (barcode P.activities) (Pattern (flags P.p.threshold U)) (fun i => A.K.hard t i U) =
      fun pack => packet P.activities P.p (A.K.hard t) U pack := by
    funext pack
    exact shovel P.activities _ U P.p pack
  have regrouped := field_eq (barcode P.activities) (flags P.p.threshold U) (fun i => A.K.hard t i U) witnessed.2
    (same.symm ▸ packetSummable)
  rw [same] at regrouped
  have atBox (box : Box n) : grouped P o A.K Finset.univ t box U =
      cram (barcode P.activities) (fun i => A.K.hard t i U) box := by
    unfold grouped
    rw [entries A t]
    rfl
  rw [funext atBox]
  exact regrouped.symm

include positive in
theorem density {a q h : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid w P.p.B a q)
    (hard : A.K.Paid w P.p.B a h) (t : T) (U : Config G n) :
    A.density t U = (Real.exp (P.exponent U) : ℂ) •
      (Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) *
        Poly.pass (WilsonPhysicalHistoryGroupedClear.localLog A.E t U) *
        field (fun box => grouped P o A.K Finset.univ t box U) (flags P.p.threshold U)) := by
  unfold Gallery.density
  rw [gas A w positive expo hard t U, WilsonPhysicalHistoryGroupedClear.factored A.E w positive expo reg t U]

end YM.Integration.WilsonPhysicalHistoryGroupedGas
end

