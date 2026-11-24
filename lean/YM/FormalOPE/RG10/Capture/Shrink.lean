import YM.FormalOPE.RG10.Capture.Depot
import YM.FormalOPE.RG10.Transit.Remote

/-!
# Cost after applying ONE far test to a *whole* intrinsic kernel

No dependence on number of lattice sites except the stated occupancy bound. Restore announced
horizon m in scale t convention through any such transaction. This can in particular be used on
invariant signed matched remainders after projecting them with all test-dependence retained.
Does not silently feed address/jet terms with unit-test rather than displaced probes. This
'smooth macro center' convention means test-derivatives are also at far-scale envelope. If one
wants pointlike center in near units, need an adapter using e.g. translation/rotation and
profile approximation; not asserted here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Function Finset MeasureTheory Filter Route Transit
open scoped Topology BigOperators Classical
variable {X : Type} [MeasurableSpace X] {T U : ℕ→ Type} {α β : Type*}
variable (W : Scale X U) (S : Locale T X α β)

structure Occupancy (t : ℕ) (C : ℝ) (i : ℕ) (A : Lens W.tape) (φ : α) : Prop where
  count : ∃ L : Finset (T i),
    (∀ z∈L, ∀ x∈S.park i z,∀ v, ‖S.differential i v φ x‖ ≤ C*((W.μ t)^4)⁻¹) ∧ -- parentheses!
    (∀ z∈L, A.m (S.point i z) ≤ C*W.μ i) ∧
    (∀ z∉L, ∀ x∈S.park i z,∀ v, S.differential i v φ x=0) ∧
    ((L.card:ℝ) ≤ C * (W.μ t/W.μ i)^4)
variable (φ : α) (A : Lens W.tape) {t n r b i m:ℕ} (P : Skin T U α i) {C K : ℝ}
local notation "R" => W.μ t
local notation "μ" => W.μ i
local notation "q" => (R^4)⁻¹
variable (hp: 2 ≤ C) (hc : (r:ℝ)+1 ≤ C) (z : T i)
variable (he : Fits W S i P n r K)

include he hc hp
private lemma used_one (h : ∀ x∈ S.park i z, ∀ v, ‖S.differential i v φ x‖ ≤ C*q)
    (h' : A.m (S.point i z) ≤ C*μ) : W.value i n r A (P z φ) ≤ C^(2*n+2)*K*q := by
  let B:= W.tape.sphere (S.point i z) 0
  have h0 : 0 ≤ C:= by linarith
  have hμ := W.positive i; have hR:= W.positive t; have hq : 0 ≤ q := by positivity
  have hK : 0 ≤ K:= by obtain ⟨Q,_,_,he⟩:= he 0 (Nat.zero_le _) z; exact (Q.worthAt_nn ..).trans he
  have hm (a:X) : A.m a ≤ C*μ + B.m a := by
    have hh : B.m a=W.tape.Δ (S.point i z) a := by unfold B Tape.sphere; simp [max_eq_right (W.tape.sign _ a)]
    rw [hh]; linarith [A.path a (S.point i z)]
  have hh (j : ℕ) (hj : j∈range (r+1)) : worth (W.eyes i B) n (coeff j (P z φ)) ≤ K*(C*q) := by
    obtain ⟨Q,H,H',HQ⟩:= he j (Nat.le_of_lt_succ (mem_range.mp hj)) z
    rw [H]; exact (Strip.prices W n H' h).trans (mul_le_mul_of_nonneg_right HQ (by positivity))
  have hZ : W.value i n r B (P z φ) ≤ C*(K*(C*q)) := (Finset.sum_le_sum hh).trans (by rw [sum_const, nsmul_eq_mul, card_range, Nat.cast_add_one]; exact mul_le_mul_of_nonneg_right hc (by positivity))
  apply (W.shift i A B n r _ (show 0 ≤ C*μ by positivity) hm).trans
  rw [mul_div_cancel_right₀ _ (W.positive _).ne']; apply le_trans (b:=(C^2)^n * (C*(K*(C*q)))) (mul_le_mul (pow_le_pow_left₀ (by linarith) (show 1+C≤C^2 by nlinarith) _) hZ (W.nn ..) (by positivity)); exact Eq.le (by rw [pow_add,pow_mul]; ring)

include he
omit hp hc in
lemma shadow (h : ∀ x ∈ S.park i z,∀ v,S.differential i v φ x=0) : W.value i n r A (P z φ) = 0 := by
  unfold Scale.value mag; apply Finset.sum_eq_zero; intro j hj; obtain ⟨Q,hQ,hT,hR⟩:= he j (Nat.le_of_lt_succ (mem_range.mp hj)) z; rw [hQ,Strip.dead hT h,worth_empty]

/-- The *full* genuine moment bound from Occupancy. Ratio of scale-to-far absorbed from
occupancy vs profile derivative costs, engineering factor not cancelled. -/
theorem restored [∀ i,Fintype (T i)] (h : Occupancy W S t C i A φ) (hK : 0 ≤ K) :
   W.value i n r A (fingerprint φ W m b i P) ≤ (W.μ b/W.μ i)^m * C^(2*n+3)*K := by
  obtain ⟨X,H⟩:=h.count; obtain ⟨H,H',hs,hZ⟩:=H
  let T := (W.μ b/W.μ i)^m * (μ^4); have hC : 0≤ C:=by linarith
  have hi:= W.positive i; have ht:= W.positive t; have hb:= W.positive b
  have hT : 0≤T:=by unfold T; positivity
  let Y:=C^(2*n+2)*K*q; have hY : 0 ≤ Y:= by unfold Y; positivity
  change mag _ _ _ (nominal T • _ )≤ _; rw [nominal_mag T hT]; apply (mul_le_mul_of_nonneg_left (W.sum' ..) hT).trans; rw [← Finset.sum_subset (Finset.subset_univ X) (fun z _ hz => shadow W S φ A P z he (hs z hz))]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun z hz => used_one W S φ A P hp hc z he (H z hz) (H' z hz))) hT)
  rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ hY) hT).trans
  exact le_of_eq (by unfold Y T; simp_rw [div_pow]; field_simp; ring)
end YM.FormalOPE.RG10.Capture
