import YM.LocalLTE.Port.Shift
/-! # E and K projections from finite packs (prior to transmission)
record E rays and K per-source even when slots shared. Aggregations located in committed markers. Keep UNIT separate. Use menus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J:Type}[DecidableEq V][Fintype V](R: Marker.Census V) (B:Bands R Q)(r:V→ℝ)(o:V→Site f)
variable [Fintype I](M:I→Menu.Hat R Q)
omit [Fintype V] in
lemma fee_mono (b:R.Mode)(F f':V→ℝ)(hf:∀ i,0≤ f' i)(he:∀ i,f' i≤F i): Marker.Poly.toll f' b≤Marker.Poly.toll F b:= prod_le_prod (fun i _=>hf i) (fun i _=> he i)
section sums
variable [Fintype J] (F':J→Menu.Hat R Q)(U:Config G f)
local notation "Y"=> Sum.elim M F'
def originQ (M:Menu.Hat R Q):= M.s.val.image o⊆M.M.crest
omit [Fintype V] in
lemma grouped : roll Y U= Menu.roll M U+ Menu.roll F' U:=by
    let Q:= Y; have hz(k): Menu.rush Q k U=Menu.rush M k U+ Menu.rush F' k U:=by rw [Menu.rush,Fintype.sum_sum_type];rfl
    have hp (m) (h:m∈logDeck M):m∈logDeck Q:=by obtain ⟨i,hi⟩:= (cams M m).1 h; exact (cams Q m).2 ⟨Sum.inl i,hi⟩
    have hq (m) (h:m∈logDeck F'):m∈logDeck Q:=by obtain ⟨i,hi⟩:= (cams F' m).1 h; exact (cams Q m).2 ⟨Sum.inr i,hi⟩
    unfold roll; change (∑ i∈ logDeck Q,rush Q (.logKey i) U) =_
    simp_rw [hz]; rw [Finset.sum_add_distrib]; refine congr_arg₂ (·+·) (sum_subset (fun i hi=>hp _ hi) (fun p h hx=> rush_vacuous M (.logKey p) U (fun i h=>hx ((cams _ p).2 ⟨i,h⟩)))).symm (sum_subset (fun i hi=>hq _ hi) (fun p h hx=>rush_vacuous F' (.logKey p) U (fun i h=>hx ((cams _ p).2 ⟨i,h⟩)))).symm
omit [Fintype V] in
lemma registered (p:Box f): Menu.board Y p U = Menu.board M p U+ Menu.board F' p U:=by
    have he(j): (Menu.rush Y j U) = Menu.rush M j U+ Menu.rush F' j U := by rw [Menu.rush,Fintype.sum_sum_type];rfl
    unfold board; simp_rw [he]; rw [Summable.tsum_add]; exact (chair M U).comp_injective Subtype.val_injective; exact (chair F' U).comp_injective Subtype.val_injective
end sums
variable (U:Config G f)
def tags (R: Marker.Census V)(M: I→Menu.Hat R Q) : Prop:= ∀ j i k,(M i).M.turn=.logKey j→ (M k).M.turn=.logKey j→ i=k
omit [Fintype V] in
lemma recordedE (he:∀ i: I, ∃ k,(M i).M.turn=.logKey k): Menu.board M=0:=by
    unfold board; funext p U; exact (tsum_congr fun j=> rush_vacuous _ _ _ (fun i h=>by obtain ⟨k,hp⟩:=he i; unfold WKey at h; rw [h] at hp; contradiction)).trans tsum_zero
omit [Fintype V] in
lemma recordedK (he:∀ i: I, ∃ k,(M i).M.turn=.gasKey k): Menu.roll M=0:=by
    unfold roll; funext U; exact sum_eq_zero fun j _=> rush_vacuous _ _ _ (fun i h=>by obtain ⟨k,hp⟩:=he i; unfold WKey at h; rw [h] at hp; contradiction)
omit [Fintype V] in
lemma rollCall (hx:∀ i,∃ k,(M i).M.turn=.logKey k): roll M U=∑ i, amount (M i) U :=by
    unfold roll rush; rw [sum_comm]; apply sum_congr rfl; intro i _
    obtain ⟨v,h⟩:=hx i; rw [sum_eq_single v]; exact if_pos h
    · intro b _ hp; exact if_neg fun ht=>hp (Lotus.Wing.logKey.inj (ht.symm.trans h))
    intro ht; exact False.elim (ht ((cams M v).2 ⟨i,h⟩))
variable (hU: HasSlots Q.p Q.activities) (β : Type*)
section
-- total series.Index tests / capacities.Charges.
variable (t:ℕ→ℝ)(u:ℕ×ℕ→ℝ)
end
end YM.LocalLTE.Port
