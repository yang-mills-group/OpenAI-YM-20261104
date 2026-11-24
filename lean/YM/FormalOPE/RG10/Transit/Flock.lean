import YM.FormalOPE.RG10.Transit.Union

/-!
# One moving step join of arbitrary-many tested insertions

No restrictions on the number of ways graph vertices hook onto marks; the binary estimate already
prices those subgraph choices polynomially in post-block supplies with fixed powers. Drop ALL
except the separate transmission, i.e. charge all corrected clusters. Full products and roots
retained before this. Power losses evaluated later. Lenses include TEST addresses in using the
input bounds (owner RG08/09 single-mark sector).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit
open Route PowerSeries Finset Function
open scoped Topology BigOperators Classical
variable {U J : ℕ → Type} {X : Type} [∀ i, Fintype (J i)]
variable {I : Type*} [DecidableEq I] (V : Voyage U J) (W : Scale X U)
variable (j : ℕ) (v : Finset I)
local notation "ι" => j+1
namespace Flock
variable (P : I→ Channel (U (j+1)))

def leakage := (V.sail j).floats (∏ k∈v,P k)-∏ k∈v,(V.sail j).floats (P k)

lemma split {k : I} (h:k∉v) : leakage V j (insert k v) P =
    (V.sail j).error (P k) (∏ l∈v,P l) +
    (V.sail j).floats (P k) * leakage V j v P := by
  unfold leakage Episode.error; rw [prod_insert h,prod_insert h]; ring
omit [DecidableEq I] in
@[simp] lemma lone (k:I) : leakage V j {k} P=0 := by simp [leakage]
omit [DecidableEq I] in
@[simp] lemma quiet : leakage V j ∅ P=0 := by simp [leakage]

local notation "T" => W.tape
variable (Y : I→ Lens W.tape) (O : Lens W.tape) {C L : ℝ}
variable [∀ i, Fintype (U i)] [∀ i,DecidableEq (U i)]
variable (u : Finset I) (r n d : ℕ) (D : I→ℕ) (S : I→ℝ)
    (h : V.regular W r d n j C) -- needs instances order reposition
local notation "ω" => tip (L/W.μ j) n
local notation "p" => Episode.pressure r d
local notation "N" => Episode.momentIn r d n

variable (ht : ∀ k∈u, Guard (P k) r (D k)) (hd : ∑ k∈u,D k ≤ d)
    (hL : 0 ≤ L) (hp : ∀ k∈u, O.m ≤ (Y k).m) (hq : ∀ k∈u,∀ l∈u,k≠l→ (Y k).Spaced (Y l) L)
    (hv : ∀ k∈u, W.value (j+1) (Episode.momentIn r d n) r (Y k) (P k) ≤ S k)
    (hc : ∀ k∈u, W.value j n r (Y k) ((V.sail j).floats (P k)) ≤ S k)
include ht hd hL hp hq hv hc h in

theorem priced (hu:v⊆u) : ω * W.value j n r O (leakage V j v P) ≤ v.card * (C^p * ∏ k∈v,S k) := by
  have h' := h.width.hi
  have hC : 0 ≤ C:=by linarith
  have hs k (hk:k∈u) : 0≤ S k:= (W.nn ..).trans (hv k hk)
  have hy : 0 ≤ ω := (tip_pos (div_nonneg hL (W.positive j).le) _).le
  induction v using Finset.induction with
  | empty=> simp
  | insert k v H ih =>
    have hk : k∈u:=hu (mem_insert_self ..); have hA : v ⊆ u:=by exact (subset_insert ..).trans hu
    have hS := hs k hk; let Q:=∏ k∈v,S k; have hQ : 0 ≤ Q:= prod_nonneg fun i hi => hs _ (hA hi)
    obtain rfl|hN:= v.eq_empty_or_nonempty
    · simp only [insert_eq,union_empty,lone,Scale.zero,card_singleton, Nat.cast_one, prod_singleton,mul_zero]; positivity -- inspect
    rw [split V j v P H,prod_insert H,card_insert_of_notMem H]; push_cast
    let A:= Lens.region Y v hN
    have hm : W.value ι N r A (∏ l∈v, P l) ≤ Q := by
      apply (mag_prod _ _ _ (W.alive ι A) _ _).trans; exact prod_le_prod (fun _ _=>W.nn ..) fun l hl => (W.mono ι A (Y l) N r (P l) (Lens.region_le Y hN l hl)).trans (hv l (hA hl))
    have H0:= V.event W r d n (Y k) A O (Lens.under_region O Y hN fun i hi=> hp _ (hA hi)) (hp _ hk) (Lens.spaced_region (Y k) Y hN (fun i hi=> hq k hk i (hA hi) (fun h => H (h ▸ hi)))) hL h (Guard.mono (ht k hk) ((single_le_sum (f:=D) (fun i _ => Nat.zero_le _) hk).trans hd))
      (Guard.mono (Guard.prod v P D (fun i hi=> ht _ (hA hi))) ((sum_le_sum_of_subset hA).trans hd))
    -- can replace aux: event implicit below
    apply (mul_le_mul_of_nonneg_left (W.add ..) hy).trans; rw [mul_add]; refine (add_le_add (d:=S k * (v.card*(C^p*Q))) (H0.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hv _ hk) (by positivity)) hm (W.nn ..) (by positivity))) ?_).trans ?_ -- first sub goal
    · exact (show ω*W.value j n r O ((V.sail j).floats (P k)* _) ≤ S k * (v.card*(C^p * Q)) from calc
         _ ≤ ω*(W.value j n r O ((V.sail j).floats (P k))*W.value j n r O (leakage V j v P)) := mul_le_mul_of_nonneg_left (W.mul ..) hy
         _ ≤ S k * (ω * W.value j n r O (leakage V j v P)) := by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_right ((W.mono j O (Y k) n r _ (hp _ hk)).trans (hc _ hk)) (mul_nonneg hy (W.nn ..)) -- inspect
         _ ≤ _ := mul_le_mul_of_nonneg_left (ih hA) hS)
    unfold Q; exact le_of_eq (by ring)
end Flock
end YM.FormalOPE.RG10.Transit
