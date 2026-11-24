import YM.OPE.Frame.Price
/-!
# One layer at every horizon with possibly moving external neighbors
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
local notation "hP" => F.phase.transport
local notation "V" => Z.representation
local notation "P" => F.phase.transport.spots
local notation "A'" => deploy ∘ A
variable (hT : Tendsto T l atTop) [l.NeBot] (H : Services C U S) (n : ℕ)
    (hr : Tendsto r l (𝓝[>]0)) (w : L → Viewers F)
include hT H hr
/-- Includes zero rate when X, O still describes a cluster tending to collapse. -/
lemma coeff_cost (hb : 0 ≤ b) (ha : Tendsto (fun k=> away (X k) (O k)) l (𝓝 0))
    (hx : Kept l T b X) (he : enveloped l T b X O) :
    RateLE l T (fun i=> Z.coeff (r i) p A (X i) (O i)) (((load A:ℝ)-(p.fst:ℝ))*b) := by
  let σ:= (load A:ℝ)
  rcases hb.eq_or_lt with hb|hb; subst b
  · rw [mul_zero]; let D:=Z.sampling p.fst
    have hp : RateLE l T (fun k=> assess R χ D (X k) A (O k)) 0 := by
      apply (assess_price (g:=fun _ _ _ _=>0) (F:=F) (a:=0) hT A D (fun _ _=>0)
        (Eventually.of_forall fun k t=>by simp) (Eventually.of_forall fun k b e => by simp)
        (cleared_footprints D ha hx.inject) ?_).congr (Eventually.of_forall fun i=>by simp)
      intro e b K; let C' (i:Fin e.val.n):= (e.val.letter i).fst; let B k:= escorts e.val (O k) (K k)
      obtain ⟨ht,_⟩ := escort_bounds hT e.val O K
      let W k : MultilinearMap ℂ (fun i=> S.Field (C' i)) ℂ := (sensed S S (beside (X k) (B k)) (beside (fun i=>(A i).fst) C')).currySum (fun i=>(A i).snd)
      have hh k x : W k x=sense S (beside (X k) (B k)) (beside A (fun i=>⟨C' i,x i⟩)) := beside_sensed A x
      have h x : RateLE l T (fun k=>W k x) 0:= by simp_rw [hh]; exact (sense_base (F:=F) A _ hT H (fun _=>none) hx ht (escorts_room hT e.val ha K) le_rfl le_rfl).mono (by simp)
      simp only [sub_zero]; exact (met hT W h (fun k=> readAs R χ e b (K k)) (fun j=> rotating_bound hT _ (F.phase.transport.spots.spin _ _) K)).congr (Eventually.of_forall fun i=> hh i _)
    exact (mapped hT hp (LinearMap.toContinuousLinearMap ((Z.representation.coord p p.fst).restrictScalars ℝ))).congr ((Z.on_tail p A hr).mono fun i hi=>(hi (X i) (O i)).symm)
  obtain ⟨K,hK⟩ := Prescription.chosen F.room.kernel.laws.toSymmetric F.phase.transport.injection
  let W k := shadow K p.fst (X k) A' (O k)
  have hu : RateLE l T (fun k=> Z.representation.coord p p.fst (W k)) ((σ-(p.fst:ℝ))*b) := by
    -- applies to coord on its own grade: only grade p.fst survives.
    unfold W shadow; simp_rw [map_sum,map_smul]; refine RateLE.sum hT fun i hi=> ?_
    rcases (((full_bands ..).mp hi).eq_or_lt) with hv|hv
    · have he:= available_cost F K A' hT H hK he hx hb i
      exact (he.smul (RateLE.const _ hT)).mono (by simp only [hv,add_zero]; rfl)
    -- `i` lower grade
    have hl:= Prescription.cost K i hi
    simp_rw [hl,Z.representation.coord_lift F.room.kernel F.phase.transport.injection, Z.representation.beyond_zero _ hv,LinearMap.zero_apply, smul_zero]; apply RateLE.zero
  exact ((from_old Z p A hK hT H hr hx he hb p.fst).mono (by nlinarith only [hb]) |>.add hu hT).congr (Eventually.of_forall fun i=>sub_add_cancel ..)

namespace Scheme
omit hT H hr [l.NeBot]
def residue (T : Table C.book) (n : ℕ) (r : ℝ) (A : I → S.Tag) (x : I → E4) (o : E4) (y : J → E4) (B : J → S.Tag) :=
    sense T (beside x y) (beside A B) - ∑ i ∈ limits Z.rings n, Z.coeff r i A x o * sense T (beside (sole o) y) (beside (sole (Z.representation.label i)) B)
def remainder (n : ℕ) (r : ℝ) (A : I → S.Tag) (x : I → E4) (o : E4) (y : J → E4) (B : J → S.Tag) : F.α.unselected.algebra :=
    viewing F (beside x y) (deploy ∘ beside A B) - ∑ i ∈ limits Z.rings n, Z.coeff r i A x o • viewing F (beside (sole o) y) (deploy ∘ beside (sole (Z.representation.label i)) B)
lemma phase_error (n : ℕ) (r : ℝ) (x : I → E4) (o : E4) (y : J → E4) (h : Injective (beside x y)) (h' : Injective (beside (sole o) y)) (w : Viewers F) :
    Z.residue (spectator F w) n r A x o y B = glance F w (Z.remainder n r A x o y B) := by
  unfold residue sense remainder; rw [map_sub, map_sum]; simp_rw [map_smul, glance_sees F w _ _ h, glance_sees F w _ _ h']; rfl
end Scheme
include hT H hr
lemma discrepancy_cost (hx : Kept l T b X) (he : enveloped l T b X O)
    (h : Intervals l T s (fun k=> sole (O k)) Y) (hY : Kept l T v Y) (hs : s < b) (hb : 0 ≤ s) (hy : s ≤ v) :
    RateLE l T (fun k=> Z.residue (spectator F (w k)) n (r k) A (X k) (O k) (Y k) B)
      ((load A:ℝ)*b - (n+1:ℝ)*(b-s)+(load B:ℝ)*v) := by
    obtain ⟨K,hK⟩ := Prescription.chosen F.room.kernel.laws.toSymmetric F.phase.transport.injection
    let W k := shadow K n (X k) A' (O k); let g k i:= sense (spectator F (w k)) (beside (sole (O k)) (Y k)) (beside (sole (Z.representation.label i)) B); let t:=(load B:ℝ)*v; let σ:=(load A:ℝ)*b
    have h' : ∀ᶠ k in l, Injective (beside (sole (O k)) (Y k)) := ((Kept.sole l T O v).chorus hY (h.mono hy)).inject
    have ha (i:Row Z.rings) : RateLE l T (fun k=>g k i) ((i.fst:ℝ)*s+t) :=
      (sense_base (sole (Z.representation.label i)) B hT H w (Kept.sole l T O s) hY h hb hy).mono (by rw [sight]; rfl)
    have hv : ∀ᶠ i in l, (∑ j ∈ limits Z.rings n, Z.representation.coord j n (W i) * g i j) = sense (spectator F (w i)) (beside (sole (O i)) (Y i)) (beside (sole ⟨n,W i⟩) B) := by
      filter_upwards [h'] with i hi; let U:=insertField S (spectator F (w i)) (O i) (Y i) B
      have hw(j a) : U j a=sense (spectator F (w i)) (beside (sole (O i)) (Y i)) (beside (sole ⟨j,a⟩) B) := inserted B _ (spectate F _).laws.toSymmetric (spectate_respects F _) hi
      conv_rhs=> rw [← hw, ← Z.representation.balance F.room.kernel F.phase.transport.injection (W i),map_sum]
      refine Finset.sum_congr rfl fun j hj=>?_ ; rw [map_smul, Z.representation.lower_weight j hj]; exact congrArg (Z.representation.coord j n (W i) * ·) ((insert_hold B (Z.representation.field j) (spectate F (w i)).laws.toSymmetric (spectate_respects F _) (spectate_ready F _) _ hi).trans (hw ..) |>.symm) -- direction `insert_hold` relates to U?
    have hf : RateLE l T (fun i=> ∑ j∈ limits Z.rings n, (Z.coeff (r i) j A (X i) (O i) - Z.representation.coord j n (W i))*g i j) (σ-(n+1:ℝ)*(b-s)+t) := by
      refine RateLE.sum hT fun j hj => ((from_old Z j A hK hT H hr hx he (lt_of_le_of_lt hb hs) n).mul (ha j)).mono ?_; unfold σ
      nlinarith only [(mul_le_mul_of_nonneg_right (show (j.fst:ℝ) ≤ n from by exact_mod_cast (bracket ..).mp hj) hb),hb] -- algebra
    exact ((old_fit A B hK hT H w hx he h hY hs hb hy n).sub hf hT).congr (hv.mono fun i hi=> by simp_rw [sub_mul]; unfold Scheme.residue; rw [Finset.sum_sub_distrib]; change _ - sense _ _ (beside (sole ⟨n,W i⟩) B) - (_ - _) = _; rw [hi]; exact sub_sub_sub_cancel_right ..) -- lemma?

omit H hT hr [l.NeBot] in
/-- Pass back to operator norm on ground errors. `rate` holds along all selections
of Viewers; the resulting ground bound also controls unselected and every selection. -/
lemma whole_cost_aux (h : ∀ᶠ i in l, Injective (beside (X i) (Y i))) (hh : ∀ᶠ i in l, Injective (beside (sole (O i)) (Y i)))
    (hp : ∀ w:L→Viewers F, RateLE l T (fun k=> Z.residue (spectator F (w k)) m (r k) A (X k) (O k) (Y k) B) u) :
    RateLE l T (fun k=> Z.remainder m (r k) A (X k) (O k) (Y k) B) u := by
  intro d hd; filter_upwards [universalize (p:=fun i w=> ‖Z.residue (spectator F w) m (r i) A (X i) (O i) (Y i) B‖ ≤ Real.exp (d*T i)) (fun w=>hp w d hd),h,hh] with i hf he hh
  exact (glance_contract F (Real.exp_nonneg _)).mpr fun w=> by rw [← Z.phase_error A B _ _ _ _ _ he hh]; exact hf w
lemma grounded (hx : Kept l T b X) (he : enveloped l T b X O) (h : Intervals l T s (fun k=> sole (O k)) Y) (hY : Kept l T v Y) (hs : s < b) (hb : 0 ≤ s) (hy : s ≤ v) :
    RateLE l T (fun k=> Z.remainder n (r k) A (X k) (O k) (Y k) B)
      ((load A:ℝ)*b - (n+1:ℝ)*(b-s)+(load B:ℝ)*v) := by
    refine whole_cost_aux Z A B ((hx.mono (le_max_left b v)|>.chorus (hY.mono (le_max_right ..)) ((Rec_spacing hT h he hs).mono (hy.trans (le_max_right ..))))|>.inject) ((Kept.sole l T O v|>.chorus hY (h.mono hy))|>.inject) (fun w=> discrepancy_cost Z A B hT H n hr w hx he h hY hs hb hy)
end YM.OPE.Frame
