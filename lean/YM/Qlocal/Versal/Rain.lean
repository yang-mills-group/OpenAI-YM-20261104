import YM.Qlocal.Versal.Drought
import YM.Next.SCHEDULE.Resize
/-!
# The real momentum read
 All periods. Actual flag mask required for prices. Calendar purchase later, but non-varying-parameter price geometry given. Support includes all root and emitted curvature paths; query can keep even more points. Theta model (group-output kernel, including `tan=true` optional) is REAL and does not bake in any local chart or log. Estimate path winding lengths and exposures before projection/coupling. Keep θ threshold normalization (not crude positive estimate off mask).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Vase
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
variable (l:Lattice.Order){s:Senses R}(A:Vase s G n)(x:Site c)(W:Config G c)(o:Site c)(p:BudgetPoint)
set_option quotPrecheck false
-- location estimates at covers.On-pre support exponent.
local notation "Ξ" => A.momentum

open Next.Scheduling Corona
variable {b:ℕ}
-- adapted `private` estimate in Scheduling.Circuit
private lemma routes {N:Side} (l : Walk) (x : Cover) (o : Site N) : ∃ f : ℕ → Site N,f 0 = wrap N x+o ∧
    (∀ i<l.length,separation (f i) (f (i+1)) ≤ 1) ∧ ∀ y ∈ visits x l,∃ i ≤ l.length,wrap N y + o=f i := by
  induction l generalizing x with
  | nil => exact ⟨fun _ => _,rfl,fun i hi => by simp at hi,by simp [visits]⟩
  | cons a l ih =>
    obtain ⟨R,hR,ht,h⟩:=ih (x+a.vec)
    let F : ℕ → Site N
      | 0 => wrap N x+o
      | i+1 => R i
    refine ⟨F,rfl,?_,fun y hy => ?_⟩
    · rintro (_|i) hi
      · change separation _ (R 0) ≤ 1
        rw [hR,map_add,wrap_vec,separation_translate,separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]
        split
        · rw [pdist_neg]; apply pdist_step
        apply pdist_step
      apply ht i
      simp at hi; omega
    rcases List.mem_cons.mp hy with h'|h'
    · exact ⟨0,Nat.zero_le _,h' ▸ rfl⟩
    obtain ⟨i,hi,H⟩:=h _ h'; exact ⟨i+1,Nat.add_le_add_right hi _,H⟩

private lemma visitsCost {N:Side} (x : Cover) (l : Walk) (o : Site N) (M : ℕ) (hm : 0 < M) :
    M*coverNumber M ((visits x l).toFinset.image (fun x => wrap N x + o)) ≤ M+l.length := by
  obtain ⟨f,hf,hr,hg⟩:=routes l x o
  obtain ⟨D,H,hD,Hh⟩:=itinerary f _ M hr hm
  rw [Nat.add_comm]; apply le_trans _ hD; apply Nat.mul_le_mul_left M
  apply Corona.list_cost; constructor
  · intro i hi
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hi; obtain ⟨v,hV,hh⟩:=hg y (List.mem_toFinset.mp hy); rw [hh]; exact Hh _ hV
  refine Corona.ship_halo _ fun i hi j hj => Relation.ReflTransGen.mono ?_ i j (H _ hi _ hj)
  rintro i j ⟨a,b,c⟩; exact ⟨a,b,c.trans (by omega)⟩


lemma sum_exits (s: Finset ι)(A:ι→ Support c)(H:Support c)(i:Site c)(hi:i∈H)(hh:∀ j∈s,¬Disjoint H (A j)) : coverNumber b (H∪s.biUnion A) ≤ coverNumber b H+∑ j∈s,coverNumber b (A j):= by
 induction s using Finset.induction_on with
 | empty => simp
 | @insert j s hz ih=>
   obtain ⟨k,hk,he⟩:= not_disjoint_iff.mp (hh j (mem_insert_self ..)); rw [biUnion_insert, Finset.union_left_comm,Finset.union_comm (A j) _, sum_insert hz]; apply le_trans (Corona.meets_sum (mem_union_left _ hk) he b); grind -- no positivity disability check
local notation "Π"=> A.cone l x
lemma crown_birth (w:Walk): x∈Crown w x:= (found_crown w x).symm ▸ List.mem_toFinset.mpr (visits_originT x w) where visits_originT (x:Site c)(w:Walk): x∈visits x w:= by cases w<;> simp [visits]
lemma singleton_cost (i:Site c): coverNumber b ({i}:Support c) ≤ 1 := calc
 _ ≤ ({i}:Support c).card := Corona.list_cost b ⟨halo_subset b {i}, Corona.ship_halo _ (fun i hi j hj => by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
 _ = 1 := by simp
lemma paths_tube (hb:0 < b) : b*coverNumber b (cone l A x) ≤ b*(1+(essence s).card+n)+A.momentum := by
 let D:= {x}∪ (essence s).biUnion (fun i=> Crown (route 0 (A.stage.pursue i) l) x)
 have ht:coverNumber b (A.cone l x) ≤ coverNumber b D+∑ j:Fin n,coverNumber b (Crown (A.maps j).tour x):= by
   unfold cone coin Bay.site; rw [Finset.image_union,Finset.biUnion_image,Finset.image_insert,Lasso.bent,map_zero,zero_add,Finset.biUnion_image, ← Finset.singleton_union] -- Lasso name
   exact sum_exits univ _ D x (mem_union_left _ (mem_singleton_self _)) (fun i _=> not_disjoint_iff.mpr ⟨x,(mem_union_left _ (mem_singleton_self _)), crown_birth x _⟩)
 have hh:b*coverNumber b D≤ b* (1+(essence s).card)+A.stage.tariff:= calc
    _ ≤ b * (coverNumber b {x}+∑ i∈ essence s,coverNumber b (Crown (route 0 (A.stage.pursue i) l) x)) := Nat.mul_le_mul_left b (sum_exits _ _ {x} x (mem_singleton_self _) (fun i _=> not_disjoint_iff.mpr ⟨x,mem_singleton_self _,crown_birth x _⟩))
    _= b*coverNumber b {x}+∑ i∈ essence s,b*coverNumber b (Crown (route 0 (A.stage.pursue i) l) x) := by rw [Nat.mul_add,Finset.mul_sum]
    _≤ b*1+∑ i∈ essence s,(b+size (A.stage.pursue i)) := Nat.add_le_add (Nat.mul_le_mul_left b (singleton_cost ..)) (Finset.sum_le_sum fun i _=> (visitsCost 0 (route 0 (A.stage.pursue i) l) x b hb).trans_eq (by rw [route_length,sub_zero]))
    _= b* (1+(essence s).card)+A.stage.tariff:= by simp only [sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Bay.tariff,mul_add,Nat.cast_id]; ring
 obtain ht:= Nat.mul_le_mul_left b ht; rw [Nat.mul_add,Finset.mul_sum] at ht
 have hf(j:Fin n): b*coverNumber b (Crown (A.maps j).tour x)≤ b+((A.maps j).range+(A.maps j).tour.length):= le_trans (visitsCost _ _ x b hb) (by omega)
 refine ht.trans ((Nat.add_le_add hh (Finset.sum_le_sum fun j _=>hf j)).trans_eq ?_); rw [Finset.sum_add_distrib]; unfold momentum reach; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]; ring
structure Carrier (D v:ℕ)(b:ℕ)(X : Support c) : Prop where
   complete : A.cone l x ⊆ X
   reach (z:Site c)(i:z∈X) : separation x z ≤ A.momentum+v
   cost : b*coverNumber b X ≤ b*D +A.momentum
lemma Carrier.used {b':ℕ}{X:Support c} (h:Carrier l A x i b b' X):x∈X:= h.complete (A.birthplace ..)
lemma thin (hz:0<b) : Carrier l A x (1+(essence s).card+n) 0 b (cone l A x):= ⟨Finset.Subset.refl _,fun i=> radius l A x i, A.paths_tube l x hz⟩
-- ORDER: `A.X.radius`. Foot explicit, hull wakes.
variable (o': V→Site c) (S: V→Support c){v':ℕ}
noncomputable def cloak:=A.cone l x∪ (essence s).biUnion S
local notation "Δ"=> A.cloak l x S
lemma halo_cost (u:Site c): coverNumber b (halo b {u})≤1:= calc
 _ ≤ ({u}:Support c).card:= Corona.list_cost _ ⟨Finset.Subset.refl _, Corona.ship_halo _ (fun i hi j hj=>by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
 _ = 1:= by simp
lemma cloaked (hx: A.stage.Hears o') (hb:0<b) (hh:∀ j∈essence s, S j⊆halo v' {o' j})(hk:∀ j∈essence s,coverNumber b (S j) ≤ r) (hu:∀ j∈essence s, o' j∈ S j) : Carrier l A (o' (Sonnet.root s)) (1+(essence s).card+n+r*(essence s).card) v' b (cloak l A (o' (Sonnet.root s)) S):= by
 let x := o' (Sonnet.root s); refine ⟨subset_union_left,?_,?_⟩
 · intro i hi; rcases mem_union.mp hi with h|h; exact (A.radius l x i h).trans (Nat.le_add_right ..)
   obtain ⟨j,hj,ht⟩:= mem_biUnion.mp h; have hs:=hh _ hj ht; exact le_trans (separation_triangle x (o' j) i) (add_le_add (A.radius l x _ (marked l o' A hx j hj)) (by simpa only [halo_spec,mem_singleton,exists_eq_left] using hs)) -- signature radius l A not dot?
 have ht:= Nat.mul_le_mul_left b (sum_exits (b:=b) (essence s) S (cone l A x) x (A.birthplace ..) (fun i hi=> not_disjoint_iff.mpr ⟨o' i,marked l o' A hx i hi,hu i hi⟩)); rw [Nat.mul_add] at ht; have hP: (∑ j ∈ essence s,coverNumber b (S j))≤ r*(essence s).card := by simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_comm r] using Finset.sum_le_sum hk
 refine ht.trans ((add_le_add (A.paths_tube l x hb) (Nat.mul_le_mul_left b hP)).trans_eq ?_); ring
-- near canonical grouping even if path wraps (ball enough; does not remove geometry). Footprint includes addresses in proof.H.Sensor.
lemma verge (hz: A.momentum ≤ b) : Carrier l A x 1 b b (Lattice.halo b {x}) := by
 let X:= Lattice.halo b {x}
 have hf:= halo_cost (b:=b) x
 exact ⟨fun y h=> halo_spec.mpr ⟨x,mem_singleton_self _, (radius l A x y h).trans hz⟩, fun y h=> (show separation x y ≤ b from by simpa only [halo_spec,mem_singleton,exists_eq_left] using h).trans (Nat.le_add_left ..), (Nat.mul_le_mul_left b hf).trans (Nat.le_add_right ..)⟩
end YM.Qlocal.Quipu.Sonnet.Vase
