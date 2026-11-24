import YM.Comparison.RG02.Order.Restrict
import YM.FormalOPE.RG10.MarkerLog
/-! # Reconcile polarized log conventions. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Block
open Finset Function Filter Comparison Comparison.RG02
open FormalOPE.RG10 Marker Multi Extra.Trajectories Polar Word
open scoped Topology BigOperators ContDiff Classical
variable {V:Type}[Fintype V][DecidableEq V](R:Census V)(p:ℕ)
def code : Names (Order.Board R p) (budget R (Fin p)) where
    e := Embedding.refl _
    visible s:= by
       change s.val.image id∈ _; rw [Finset.image_id]
       change _∈ univ.filter _; exact mem_filter.mpr ⟨ mem_univ _,(mem_filter.mp s.property).2.1 ⟩
lemma coins (i:R.Mode)(t:Order.Index p): (code R p).share (Order.Join.pair i t)=pay i t.val := Subtype.ext (image_id)
-- directly identifies both on every component. covariant statement uses `code.restriction`,
-- which is just id on ALL slots through that order.
lemma series_of (L:Word R): (code R p).restriction (certify (Fin p) L)= Order.series R p L:= Order.Join.both_parts fun s t=> by
    change (certify _ L).part ((code R p).share _) = _; rw [coins, certify_present, Order.polarization, present_pay]
lemma series_log (L:Word R)(h:boot L=1): Order.series R p (logWord L)= connected (Order.series R p L) := by
     rw [← series_of,consistent L h, Names.connected_restrict, series_of]
     rw [certify_present,present_quiet]; exact h
lemma peel (L:Word R): PowerSeries.map (Order.blanked R) L= sing R.quiet (vac R L) := by
    apply observe_ext; intro s
    rw [see_sing]
    ext n
    rw [unfold_see, PowerSeries.coeff_map, Order.pure_marks]
    split_ifs with he <;> simp [he]
end YM.FVAAlt2.Block
