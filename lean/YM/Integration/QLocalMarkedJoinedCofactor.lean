import YM.Integration.ActualWilsonTaylorPackets
import YM.Integration.QLocalCompulsoryInventoryBank

/-! Exact surgery on the original compatible compulsory packets. The row
factors may already be signed marked polynomials. The physical index map,
guard, and dormant support/inventory slots are the original Wilson ones. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedCofactor
open Function Set Finset Lattice RG Wilson Extra.Histories Planned.GuardedAtom
open ActualWilsonPacketSplit ActualWilsonJoinedCofactor ActualWilsonTaylorSlot ActualWilsonTaylorPackets
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {α:Type*} [CommSemiring α]

def packet (W:Rep G n) (v:ℕ→α) (b:Finset ℕ) (U:Config G n) : α :=
  if W.activities.admissible W.p U b then ∏i∈b,v i else 0

def coat (W:Rep G n) (v:ℕ→α) (k:ℕ) (b:Finset ℕ) (U:Config G n) : α :=
  if k∈b ∧ W.activities.admissible W.p U b then ∏i∈b.erase k,v i else 0

def waiting (W:Rep G n) (v:ℕ→α) (S Z:Support n) (J:Finset ℕ) (U:Config G n) : α :=
  if permits W S Z J U then ∏j∈J,v j else 0

theorem flip_coat (v:ℕ→α) (k:ℕ) (J:Finset ℕ) (U:Config G n) :
    coat W v k (flip k J) U=waiting W v (scopes W k) (inventory W k) J U := by
  by_cases hk:k∈J
  · have hn:¬permits W (scopes W k) (inventory W k) J U:=by
      intro h
      obtain ⟨x,hx⟩:=(W.activities.forced k).inventory_ne.mono (W.activities.forced k).inventory_sup
      exact (Finset.disjoint_left.mp (h.2.1 k hk)) hx hx
    simp [coat,waiting,ActualWilsonJoinedCofactor.flip,hk,hn]
  · simp only [coat,waiting,ActualWilsonJoinedCofactor.flip,hk,if_false,mem_insert_self,true_and,
      ActualWilsonJoinedCofactor.attach W k J hk U,Finset.erase_insert hk]

def deposit (v f:ℕ→α) (z:Key W Y) (U:Config G n) : α :=
  if gate z U then f z.1.1 * ∏i∈z.1.2,v i else 0

def placed (K:Guard.Keeper W.p W.activities) (v f:ℕ→α) (U:Config G n) : ℕ→α :=
  Function.extend (address (Y:=Y) K) (fun z=>deposit v f z U) (fun _=>0)

theorem on_slot (K:Guard.Keeper W.p W.activities) (v f:ℕ→α) (z:Key W Y) (U:Config G n) :
    placed (Y:=Y) K v f U (address K z)=deposit v f z U :=
  (address (Y:=Y) K).injective.extend_apply ..

theorem escaped (K:Guard.Keeper W.p W.activities) (v f:ℕ→α) (i:ℕ) (U:Config G n)
    (outside:i∉Set.range (address (Y:=Y) K)) : placed (Y:=Y) K v f U i=0 :=
  Function.extend_apply' _ _ _ outside

theorem origin (v f:ℕ→α) (U:Config G n) (hot:∀r,f r≠0→¬Healthy W.p.threshold (Y r) U)
    (p:ℕ×Finset ℕ) (h:f p.1*packet W v p.2 U≠0) : (parts W Y p).1.1.Nonempty := by
  have permit:W.activities.admissible W.p U p.2:=by
    by_contra neg
    exact h (by simp [packet,neg])
  apply nonempty W (Y p.1) (parts W Y p) U _ (hot p.1 (left_ne_zero_of_mul h))
  apply (admitted_iff W _ _ _).2
  have joined:(parts W Y p).1.1∪(parts W Y p).1.2=p.2:=(partition W _).left_inv p.2
  rwa [joined]

theorem reindex (K:Guard.Keeper W.p W.activities) (v f:ℕ→α) (p:Roots W Y) (U:Config G n) :
    f p.1.1 * packet W v p.1.2 U =
       placed (Y:=Y) K v f U (place K p).1 * coat W v (place K p).1 (place K p).2 U := by
  let z:=stem p
  let b:=parts W Y p.1
  change _=placed (Y:=Y) K v f U (address K z)*coat W v (address K z) (flip (address K z) (tail p)) U
  rw [on_slot,flip_coat,(geometry K z).1,(geometry K z).2]
  have recov:b.1.1∪b.1.2=p.1.2:=recover p
  have eq:W.activities.admissible W.p U p.1.2 ↔ admitted W (Y p.1.1) b.1 U:=by
    rw [←recov]; exact (admitted_iff W _ b U).symm
  by_cases good:permits W (joined W (Y z.1.1) z.1.2) (z.1.2.biUnion (inventory W)) (tail p) U
  · have flags:=eligible W _ _ (inventory_subset W (Y z.1.1) z.1.2) _ U good
    by_cases dis:(z.1.2:Set ℕ).Pairwise (fun i j=>Disjoint (scopes W i) (scopes W j))
    · have gate:ActualWilsonTaylorSlot.gate z U:=⟨dis,flags⟩
      have yes:W.activities.admissible W.p U p.1.2:=eq.2 ⟨dis,good⟩
      rw [packet,if_pos yes,deposit,if_pos gate,waiting,if_pos good,←recov,Finset.prod_union (separated W _ b)]
      exact (mul_assoc ..).symm
    · have gate:¬ActualWilsonTaylorSlot.gate z U:=fun x=>dis x.1
      have no:¬W.activities.admissible W.p U p.1.2:=fun x=>dis (eq.1 x).1
      simp only [packet,if_neg no,mul_zero,deposit,if_neg gate,zero_mul]
  · have no:¬W.activities.admissible W.p U p.1.2:=fun x=>good (eq.1 x).2
    simp only [packet,if_neg no,waiting,if_neg good,mul_zero]

theorem target (K:Guard.Keeper W.p W.activities) (v f:ℕ→α) (p:ℕ×Finset ℕ) (U:Config G n)
    (nonzero:placed (Y:=Y) K v f U p.1*coat W v p.1 p.2 U≠0) : p∈range (place (Y:=Y) K) := by
  have present:p.1∈range (address (Y:=Y) K):=by
    by_contra absent
    exact nonzero (by rw [escaped K v f p.1 U absent,zero_mul])
  obtain ⟨z,hz⟩:=present
  let J:=flip p.1 p.2
  have back:flip p.1 J=p.2:=involution ..
  have hp:permits W (scopes W p.1) (inventory W p.1) J U:=by
    by_contra bad
    have same:coat W v p.1 p.2 U=0:=by rw [←back,flip_coat,waiting,if_neg bad]
    exact nonzero (by rw [same,mul_zero])
  have subset:Y z.1.1⊆scopes W p.1:=by rw [←hz,(geometry K z).1]; exact Finset.subset_union_left
  obtain ⟨b,old,rest⟩:=collect z J (fun j jmem=>(hp.2.1 j jmem).symm.mono_right subset)
  refine ⟨b,Prod.ext ((congrArg (address K) old).trans hz) ?_⟩
  change flip (address K (stem b)) (tail b)=p.2
  rw [old,hz,rest,back]

end YM.Integration.QLocalMarkedJoinedCofactor
