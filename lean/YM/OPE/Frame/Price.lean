import YM.OPE.Frame.Bound
/-!
# Price of the new coordinates using the all-character bounds

The mismatch of the finite `assess` fit is estimated using a **known complete**
cluster discrepancy estimate on the same hierarchy, not requiring the UV estimate
first for a smeared detector separately at cutoff. No character or cutoff
participates in the definition of `Scheme`. Single-cluster results needed here
already keep those limits in the proved order. Use the stronger `Services` of
that construction.
-/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
namespace YM.OPE.Frame
variable {G : Gauge} {C : Family G} {U : Extraction.Order} {S : Table C.book} {F : Spec.Final C U S}
    (Z : Scheme F) (p : Row Z.rings)
    {I J L : Type} [Fintype I] [Fintype J] (A : I → S.Tag) (B : J → S.Tag)
    {l : Filter L} {X : L → I → E4} {Y : L → J → E4} {O : L → E4} {T r : L→ ℝ} {b v a s u : ℝ} {m : ℕ}
local notation "Λ" => F.sector.derivatives
local notation "χ" => F.room.kernel.spin
local notation "R" => F.sector.turns
local notation "T'" => F.phase.transport -- no dots
local notation "V" => Z.representation
local notation "Z'" => Z.sampling p.fst
local notation "P" => F.phase.transport.spots
local notation "A'" => deploy ∘ A
variable {K : Prescription F.sector.derivatives} (hK : K.Coherent) (hT : Tendsto T l atTop) [l.NeBot] (H : Services C U S)
    (hr : Tendsto r l (𝓝[>]0)) (w : L → Viewers F)
include hT H
lemma sense_base (hX : Kept l T b X) (hY : Kept l T v Y) (h : Intervals l T b X Y) (hb : 0 ≤ b) (hv : b ≤ v) :
    RateLE l T (fun k=> sense (spectator F (w k)) (beside (X k) (Y k)) (beside A B)) ((load A : ℝ)*b+(load B:ℝ)*v) := by
  unfold sense; simp_rw [beside_commutes]; exact viewer_cost F H.schedule _ _ hT w hX hY h hb hv
lemma sense_alt (hX : Kept l T b X) (hY : Kept l T v Y) (h : Intervals l T v X Y) (hb : 0 ≤ v) (hv : v ≤ b) :
    RateLE l T (fun k=> sense (spectator F (w k)) (beside (X k) (Y k)) (beside A B)) ((load A : ℝ)*b+(load B:ℝ)*v) := by
  unfold sense; simp_rw [beside_commutes]; exact viewer_alt F H.schedule _ _ hT w hX hY h hb hv
include hK
local notation "N" n ":" i => shadow K n (X i) A' (O i)
lemma old_fit (hX : Kept l T b X) (he : enveloped l T b X O) (h : Intervals l T s (fun i=> sole (O i)) Y) (hY : Kept l T v Y)
    (hs : s < b) (ha : 0 ≤ s) (hy : s ≤ v) (n : ℕ) : RateLE l T (fun i=> sense (spectator F (w i)) (beside (X i) (Y i)) (beside A B) -
      sense (spectator F (w i)) (beside (sole (O i)) (Y i)) (beside (sole ⟨n,N n:i⟩) B)) ((load A:ℝ)*b-(n+1:ℝ)*(b-s)+(load B:ℝ)*v) := by
  have hp:= arrangement_cost F K n A' (deploy ∘ B) hT H hK he hX (lt_of_le_of_lt ha hs) hY h ha hy hs
  have hq:= ((Kept.sole l T O v).chorus hY (h.mono hy)).inject
  have ht:= ((hX.mono (le_max_left b v)).chorus (hY.mono (le_max_right ..)) ((Rec_spacing hT h he hs).mono (hy.trans (le_max_right ..)))).inject
  refine hp.transfer ?_; filter_upwards [hq,ht] with i hi ht
  rw [← inserted _ _ (spectate F (w i)).laws.toSymmetric (spectate_respects F _) hi, sense, beside_commutes]
  unfold insertField; rw [compatible_shadows K _ (spectate F _) (spectate_respects F _) (spectate_ready F _) _ hi, ← glance_terms F K n _ _ _ _ _ (w i) ht hi]; exact glance_bound ..

lemma towards_old (hX : Kept l T b X) (he : enveloped l T b X O) (ha : 0 < b) (n : ℕ) :
    RateLE l T (fun k=> assess R χ Z' (X k) A (O k) - assess R χ Z' (sole (O k)) (sole ⟨n,N n:k⟩) (O k))
        (((load A:ℝ)-n-1)*b) := by
  let σ (k : L) : Unit → S.Tag := sole ⟨n,N n:k⟩
  let f (k : L) (b : Bool) := investigate R χ Z' b (sole (O k)) (σ k) (O k)
  have hx : ∀ᶠ k in l, admissible Z' (X k) (O k) := cleared_footprints _ (RateLE.tends he (by linarith only [ha]) hT) hX.inject
  refine assess_price (F:=F) (g:=fun k b e K => inspect R χ e b (sole (O k)) (σ k) (O k) K) hT A Z' f (Eventually.of_forall fun _ _=> rfl)
    (Eventually.of_forall fun k t e=> inspect_live R χ P F.room.kernel (fun K=> escorts_head e.val (O k) K)) hx ?_ -- check p implicit
  intro e t Q
  obtain ⟨hw,hz⟩ := escort_bounds hT e.val O Q
  let B (i) := escorts e.val (O i) (Q i)
  let C' (j : Fin e.val.n) := (e.val.letter j).fst
  let U (p : ∀ i, S.Field (C' i)) (i : Fin e.val.n) : S.Tag := ⟨C' i,p i⟩
  let W (k) : MultilinearMap ℂ (fun i=> S.Field (C' i)) ℂ := (show MultilinearMap ℂ (fun i=> S.Field (C' i)) ℂ from (sensed S S (beside (X k) (B k)) (beside (fun i=> (A i).fst) C')).currySum (fun i=> (A i).snd)) -
      (show MultilinearMap ℂ (fun i=> S.Field (C' i)) ℂ from (sensed S S (beside (sole (O k)) (B k)) (beside (fun (_:Unit)=> n) C')).currySum (fun _=> N n:k))
  have hv k p : W k p = sense S (beside (X k) (B k)) (beside A (U p)) - sense S (beside (sole (O k)) (B k)) (beside (σ k) (U p)) := congrArg₂ (fun a b:ℂ=> a-b) (beside_sensed A p) (beside_sensed (σ k) p) -- expected types?
  have h' p : RateLE l T (fun k=> W k p) (((load A:ℝ)-n-1)*b) := by
    simp_rw [hv]; exact (old_fit (X:=X) A (U p) hK hT H (fun i=>none) hX he hz hw ha le_rfl le_rfl n).mono (by ring_nf; rfl)
  exact (met hT W h' (fun k=> readAs R χ e t (Q k)) (fun j => rotating_bound hT _ (F.phase.transport.spots.spin _ _) Q)).congr (Eventually.of_forall fun i=> hv i _)
include hr
lemma from_old (hX : Kept l T b X) (he : enveloped l T b X O) (ha : 0 < b) (n : ℕ) :
    RateLE l T (fun k=> Z.coeff (r k) p A (X k) (O k) - Z.representation.coord p n (N n:k)) (((load A:ℝ)-n-1)*b) := by
  refine (mapped hT (towards_old Z p A hK hT H hX he ha n) (LinearMap.toContinuousLinearMap ((Z.representation.coord p p.fst).restrictScalars ℝ))).congr ?_
  filter_upwards [Z.on_tail p A hr] with i hi; rw [hi (X i)]; exact (map_sub (Z.representation.coord p p.fst) _ _).trans (congrArg _ (coherent_coord Z p n (N n:i) (O i))) -- check rw
end YM.OPE.Frame
