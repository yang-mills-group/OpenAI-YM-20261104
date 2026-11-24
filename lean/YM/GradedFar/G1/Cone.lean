import YM.GradedFar.G1.Wire
/-!
# Cost an induction by a fixed growth factor NOT changing with the crop q

Pure scalar argument. A fixed per-step cost b and additive error a at that proof
node are accurate enough because this yields polynomial in the stretch. Then
reserve from increasing q can pay throughout with exponents independent of it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.G1.Wire
open Function Set Filter
open scoped Topology Classical BigOperators
variable {K:ℕ} {g:ℝ}(H:ℝ→ℝ) {A B C:ℝ}
lemma rays {r:ℕ}(hr:A+1 ≤ (2:ℝ)^r)(g₀:0<g)(a:0≤A)(b:0≤B)
    (step:∀T:ℝ, Edge K g T→Edge K g (T*2) → H (T*2) ≤ A*H T + B)
    (base:∀T:ℝ, Edge K g T→ T ≤ 2 → H T≤ B) : ∀ T:ℝ, Edge K g T → H T ≤ T^r*B := by
  have h (n:ℕ):∀ T, Edge K g T→ T≤2^n*2 → H T ≤ T^r *B := by
    induction n with
    | zero=> rintro T h b'; refine (base T h (by simpa using b')).trans (le_mul_of_one_le_left b (one_le_pow₀ h.1))
    | succ n ih =>
      intro U e hv
      by_cases h: U ≤ 2
      · exact (base U e h).trans (le_mul_of_one_le_left b (one_le_pow₀ e.1))
      let T:=U/2; have tp : 1 ≤ T := by unfold T; linarith [lt_of_not_ge h]
      have T0 : 0 ≤ T:=zero_le_one.trans tp; have c:U=T*2:= by unfold T; ring
      have ht : T≤ U := by linarith only [tp,c]
      have s := exhaust (hg:=g₀) e tp ht
      have nt: T ≤ 2^n*2 := by rw [pow_succ,c] at hv; linarith [hv]
      have start := ih T s nt; rw [c] at e ⊢
      calc _ ≤ A*(T^r*B)+B := (step T s e).trans (add_le_add (mul_le_mul_of_nonneg_left start a) le_rfl)
           _ ≤ (A+1)*T^r *B := by
             have h:= le_mul_of_one_le_left b (one_le_pow₀ (n:=r) tp); linarith only [h]
           _ ≤ _ := by rw [mul_pow,mul_comm (T^r)]; gcongr
  intro T e; obtain ⟨n,h'⟩ := pow_unbounded_of_one_lt T (by norm_num : 1 < (2:ℝ)); exact h n T e (by linarith [h',e.1])
lemma taper {v p r: ℕ} (net:p+K*r≤v)(g₀:0<g)(cap:g≤1){T:ℝ}(e:Edge K g T):T^r*g^v ≤ g^p :=
  calc _ ≤ T^r*g^(p+K*r) := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one g₀.le cap net) (pow_nonneg (zero_le_one.trans e.1) _)
       _ = T^r*g^(K*r)*g^p:= by rw [pow_add]; ring
       _ ≤ _ := mul_le_of_le_one_left (pow_nonneg g₀.le _) (receipts g₀ e r)
end YM.FVA2.GradedFar.G1.Wire
