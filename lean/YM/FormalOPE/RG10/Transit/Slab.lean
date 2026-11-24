import YM.FormalOPE.RG10.Routes.Episode

/-!
# One-regulator cutoff slab

Episodes from index `(j+1)` to `j`, in thermal coordinates before projections. Use at ANY
fixed cutoff supplying the requested formal full-weight and centering operation; this file doesn't
impose analytical bounds on their propagation. Pair error impulse for telescoping to capture or
first join with a probe. No Taylor precision losses algebraically (estimates are separate).
No inverse positivity presumed. Subring `keeping` presents invariant/not-address-erased series
eligibility in using this, not needed for algebra itself and ONLY carried as membership certificates.
It may depend on order/regulator in those applications. No assertion of completion of any
producer. Identity independent of actual physical kernel artifacts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function
open scoped BigOperators Classical
variable {U J : ℕ → Type} [∀ i,Fintype (J i)]

structure Voyage (U J : ℕ→ Type) where
  sail : ∀ i, Episode (U (i+1)) (U i) (J i)

variable (V : Voyage U J)
namespace Voyage

/-- Totalized to simplify telescopes; use only with `k≤j`. -/
def yield (k j : ℕ) : Channel (U j) →+ Channel (U k) := match j with
  | 0 => if h : k=0 then h ▸ AddMonoidHom.id _ else 0
  | i+1 => if h : k=i+1 then h ▸ AddMonoidHom.id _ else (yield k i).comp (V.sail i).floats
-- implicit V binder power issue inspect

lemma same (i) : V.yield i i=AddMonoidHom.id _ := by cases i <;> simp [yield]
@[simp] lemma sameHere (i) (x:Channel (U i)) : V.yield i i x=x := by rw [same]; rfl
lemma send_next {i k : ℕ} (h : k ≤ i) (x : Channel (U (i+1))) :
    V.yield k (i+1) x=V.yield k i ((V.sail i).floats x) := by simp_rw [yield, dif_neg (show k≠i+1 by omega)]; rfl
variable {i j k b N : ℕ}
lemma follows (h₁ : i≤j) (h₂ : j≤k) (x : Channel (U k)) : V.yield i k x=V.yield i j (V.yield j k x) := by
  induction k,h₂ using Nat.le_induction with
  | base => simp
  | succ k h ih => rw [send_next V (h₁.trans h), send_next V h, ih]
lemma approach (h : k < N) (x : Channel (U N)) : (V.sail k).floats (V.yield (k+1) N x)= V.yield k N x := by
  rw [follows V (Nat.le_succ k) h]; rw [send_next V (le_refl _),sameHere]
lemma unit (h : k ≤ N) : V.yield k N 1=1 := by
  induction N,h using Nat.le_induction with
  | base => simp
  | succ j h ih => rw [send_next V h, Episode.float_one, ih]

variable (G H : Channel (U N))
/-- Discrepancy in propagating separately vs whole transfer since scale N, at k. -/
def apart (k : ℕ) := V.yield k N (G*H)- V.yield k N G*V.yield k N H
lemma apart_step (h:k<N): V.apart G H k = (V.sail k).floats (V.apart G H (k+1)) +
    (V.sail k).error (V.yield (k+1) N G) (V.yield (k+1) N H) := by
  unfold apart Episode.error; rw [map_sub,approach V h,approach V h,approach V h]; ring

def impulse (i : ℕ) := (V.sail i).error (V.yield (i+1) N G) (V.yield (i+1) N H)

lemma telescope (h : i ≤ j) (k : j ≤ N) : V.apart G H i = V.yield i j (V.apart G H j)+
      ∑ v∈Finset.Ico i j, V.yield i v (V.impulse G H v) := by
  induction j,h using Nat.le_induction with
  | base => simp
  | succ j h ih =>
    rw [ih (by omega), apart_step V G H k, map_add, send_next V h, sum_Ico_succ_top h]; unfold impulse; abel

lemma topdown (h : k ≤ N) : V.apart G H k= ∑ v∈Finset.Ico k N,V.yield k v (V.impulse G H v) := by
  rw [telescope V G H h (le_refl _),show V.apart G H N=0 from (by simp [apart]), map_zero,zero_add]

-- supply analyticity/invariance scope prior to estimates
variable {r d : ℕ}
def Eligible (V : Voyage U J) (r k N : ℕ) := ∀ i∈ Ico k N,(V.sail i).Eligible r
-- `Episode.Eligible` doesn't require Fintype ??
variable (F : ∀ i, Subring (Channel (U i)))
def authentic (k N: ℕ) := ∀ i∈ Finset.Ico k N,∀ A∈F (i+1),(V.sail i).floats A∈ F i

variable {G H V F}
omit [∀ i,Fintype (J i)] in
lemma Eligible.clip (h:Eligible V r b N) {n} (hk:b≤k)(hi:n≤N): Eligible V r k n:= fun j hj=>h j (Finset.Ico_subset_Ico hk hi hj)
lemma authentic.clip (h:authentic V F b N) {n}(hk:b≤k)(hi:n≤N): authentic V F k n:= fun j hj=>h j (Finset.Ico_subset_Ico hk hi hj)
lemma positions (h:Eligible V r k N) (hq : Guard G r d) (hz : k ≤ N) : Guard (V.yield k N G) r d := by
  induction N,hz using Nat.le_induction with
  | base => simpa
  | succ j hj ih => rw [V.send_next hj]; exact ih (h.clip le_rfl (Nat.le_succ j)) (Episode.Eligible.forward _ _ _ (h j (by simpa)) hq)
lemma keeping (h:authentic V F k N)(hx : G ∈ F N) (hz : k≤N) : V.yield k N G ∈ F k := by
  induction N,hz using Nat.le_induction with
  | base => simpa
  | succ j hj ih => rw [V.send_next hj]; exact ih (h.clip le_rfl (Nat.le_succ j)) (h _ (by simpa) _ hx)

lemma impulse_guard {d₁ d₂ : ℕ} (h : Eligible V r k N) (hx : Guard G r d₁) (hh : Guard H r d₂) (hz : k < N) : Guard (V.impulse G H k) r (d₁+d₂) := by
  have he := h k (by simpa); have hg:=h.clip (Nat.le_succ k) le_rfl
  have hA := positions hg hx hz; have hB:=positions hg hh hz
  unfold impulse Episode.error; apply Guard.sub (Episode.Eligible.forward _ _ _ he (hA.mul hB)); exact Guard.mul (Episode.Eligible.forward _ _ _ he hA) (Episode.Eligible.forward _ _ _ he hB)
lemma impulse_closed (h:authentic V F k N) (hx : G ∈ F N) (hh : H ∈ F N) (hz : k < N) : V.impulse G H k ∈ F k := by
  have he := h k (by simpa); have hg := h.clip (Nat.le_succ k) le_rfl
  have hA := keeping hg hx hz; have hB:=keeping hg hh hz
  exact (F _).sub_mem (he _ ((F _).mul_mem hA hB)) ((F _).mul_mem (he _ hA) (he _ hB))
end Voyage
end YM.FormalOPE.RG10.Transit
