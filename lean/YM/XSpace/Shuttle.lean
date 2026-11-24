import YM.XSpace.LapCon
import YM.XSpace.Pulse

/-!
# Wires. Delete interior bilocal contractions.

Need that ∆ on the auxiliary product with an arbitrary color-scalar kernel closes back
onto the span of those products, WITHOUT repeating any position. A "shuttle" transmits
one new auxiliary leg to a previously used one. We may even use pairs on the outside with
arbitrary polarizations when applying silence tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter MvPolynomial Next.Rank.Normal
open scoped BigOperators Classical
variable {G : Gauge} {ι : Type*}
def Spots (s : Finset E4) (x y : Ph) := insert x.1 (insert y.1 s)
variable (L : Finset (World G))
abbrev cellL (x : Ph) (a : G.ColorIndex): World G:= lit x.1 x.2 a
def covers (x : Ph):= ∀ a, cellL x a∈ L
inductive Friends : Finset E4 → Pol G → Prop where
| baby (s : Finset E4): Friends s 1
| joined {S:Finset E4} {P} (x y:Ph) (he : x.1∉S) (hf : y.1∉S) (hx:x.1 ≠ y.1) (hkx : covers L x) (hky:covers L y)
    (h : Friends (Spots S x y) P): Friends S (bilocal G x y*P)
| add {S P Q}: Friends S P → Friends S Q→ Friends S (P+Q)
| smul {S P}(c:ℂ): Friends S P → Friends S (c • P)
variable {L} {S E I:Finset E4} {P : Pol G}
lemma friends_zero : Friends L S 0:= zero_smul ℂ (1: Pol G) ▸ (Friends.baby (L:=L) S).smul 0
lemma Friends.more (hp : Friends L S P) (h : E ⊆ S): Friends L E P:=by
  induction hp generalizing E with
  | baby=> exact .baby E
  | joined x y hx hy hm hab hab' hP ih=> exact .joined _ _ (fun e=> hx (h e)) (fun e=>hy (h e)) hm hab hab' (ih (Finset.insert_subset_insert _ (Finset.insert_subset_insert _ h)))
  | add _ _ ih1 ih2=> exact (ih1 h).add (ih2 h)
  | smul c _ ih=>exact (ih h).smul c
lemma Friends.fit (hp : Friends L S P): P∈Lap.scope L:= by
  induction hp with
  | baby=> exact one_mem _
  | joined x y hx hy _ hk hl hp ih=> exact Subalgebra.mul_mem _ (Subalgebra.sum_mem _ fun a _=> Subalgebra.mul_mem _ (X_mem_supported.mpr (hk a)) (X_mem_supported.mpr (hl a))) ih
  | add _ _ ih1 ih2=> exact Subalgebra.add_mem _ ih1 ih2
  | smul a hp ih=>exact (Lap.scope L).toSubmodule.smul_mem a ih
lemma Friends.acts (hp : Friends L S P) (e:G.ColorIndex) (Q : Pol G) (hx : Q∈Room G S) (hQ : Silent S Q): receive G (P*Q)=0:= by
  induction hp generalizing Q with
  | baby=> rw [one_mul]; exact hQ.self
  | @joined S P x y he hf h h1 h2 _ ih=>
    rw [mul_comm _ P,mul_assoc]; refine ih (bilocal G x y*Q) (Subalgebra.mul_mem _ ?_ (room_after _ (room_after _ hx))) (hQ.linked e hx x y h he hf)
    exact bilocal_on x y (by simp [Spots]) (by simp [Spots])
  | add _ _ ih1 ih2=>rw [add_mul,map_add,ih1 Q hx hQ,ih2 Q hx hQ,zero_add]
  | smul a hp ih=>rw [smul_mul_assoc,map_smul,ih _ hx hQ,smul_zero]

-- no consistent value across axes needed, only a color scalar
variable (K : Symmetric (World G))
def ColorLaw : Prop:=∀ x y:Ph,∃ r:ℂ,∀ a b,(K.cov (cellL x a) (cellL y b)) = if a=b then r else 0

def shuttle (x y:Ph) : Module.End ℂ (Pol G):= ∑ a:G.ColorIndex, (LinearMap.mulLeft ℂ (X (cellL x a))) ∘ₗ (slit (K.cov (cellL y a))).toLinearMap
lemma rides (x y:Ph) (p : Pol G): shuttle K x y p=∑ a:G.ColorIndex,X (cellL x a)*slit (K.cov (cellL y a)) p:= LinearMap.sum_apply ..

variable {K}
lemma sole (HK : ColorLaw K) (x y : Ph) (A B :Ph): ∃ α β:ℂ, shuttle K x y (bilocal G A B)= α • bilocal G x B + β • bilocal G x A:=by
  obtain ⟨α,hα⟩:= HK y A; obtain ⟨β,hβ⟩:=HK y B
  use α,β; rw [rides,bilocal]; simp_rw [_root_.map_sum, Finset.mul_sum]
  conv_lhs=> arg 2; intro i; rw [Finset.sum_eq_single i (fun a _ ha=> by simp only [split_leibniz,slit_X]; unfold cellL at *; rw [hα,hβ,if_neg ha.symm,if_neg ha.symm]; simp) (by simp)]
  simp only [split_leibniz,slit_X]; simp only [cellL] at *; simp_rw [hα,hβ,ite_true]; unfold bilocal; rw [Finset.smul_sum,Finset.smul_sum,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=>?_; simp_rw [← C_mul']; ring

lemma link_sum (x y:Ph) (P Q: Pol G): shuttle K x y (P*Q)=shuttle K x y P*Q + P*shuttle K x y Q:=by
  simp_rw [rides,Finset.sum_mul,Finset.mul_sum, ← Finset.sum_add_distrib, split_leibniz]; apply Finset.sum_congr rfl; intro _ _; ring

lemma Friends.shuttles (x y:Ph) (K : Symmetric (World G)) (HK : ColorLaw K) (hp : Friends L S P) (h : E ⊆ S) (ha : x.1∈ S)
    (he : x.1∉ E) (ht : covers L x): Friends L E (shuttle K x y P):=by
  induction hp generalizing E with
  | baby=> rw [rides]; simp_rw [(show ∀ i : G.ColorIndex,slit (K.cov (cellL y i)) 1=0 from fun i=> (slit _).map_one_eq_zero),mul_zero,Finset.sum_const_zero]; exact friends_zero
  | @joined S P A B hA hB hm hx hy hp ih=>
    obtain ⟨α,β,hα⟩:=sole HK x y A B; have heA:A.1∉E:= fun e=>hA (h e); have heB:B.1∉E:= fun e=>hB (h e)
    have hs : Spots E A B ⊆ Spots S A B:= Finset.insert_subset_insert _ (Finset.insert_subset_insert _ h)
    have hz : x.1≠A.1:= fun hh=>hA (hh ▸ ha); have hk : x.1≠B.1:= fun hh=>hB (hh ▸ ha)
    rw [link_sum,hα,add_mul,smul_mul_assoc,smul_mul_assoc]
    refine ((Friends.smul _ (?_ : Friends L E (bilocal G x B*P))).add (Friends.smul _ (?_ : Friends L E (bilocal G x A*P)))).add (Friends.joined A B heA heB hm hx hy (ih hs (by simp [Spots,ha]) (by simp [Spots,hz,hk,he])))
    · apply Friends.joined x B he heB hk ht hy; apply hp.more; unfold Spots; refine Finset.insert_subset ?_ ((Finset.insert_subset_insert _ h).trans (Finset.subset_insert ..)); simp [ha]
    apply Friends.joined x A he heA hz ht hx; apply hp.more; unfold Spots; refine Finset.insert_subset ?_ (Finset.insert_subset_insert _ (h.trans (Finset.subset_insert ..))); simp [ha]
  | add _ _ ih1 ih2=> rw [map_add]; exact (ih1 h ha he).add (ih2 h ha he)
  | smul c hp ih=> rw [map_smul]; exact (ih h ha he).smul c
end YM.XSpace.Legs
