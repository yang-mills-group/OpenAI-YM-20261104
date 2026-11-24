import YM.UVExt.Token

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Function Real Laurent Lattice RG Wilson
open scoped Classical BigOperators ContDiff Topology
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]
variable {f g : ℝ→E} (B B' P Q : ℝ) (K : ℕ) (hb : 0 ≤ B) (hb' : 0 ≤ B') (hx : 0 ≤ P) (hq : 0 ≤ Q)
   (hF : ContDiff ℝ ω f) (hg : ContDiff ℝ ω g)
    (hB : ∀ i t, ‖iteratedDeriv i f t‖ ≤ B * P^i) (hY : ∀ i t, ‖iteratedDeriv i g t‖ ≤ B' * Q^i)

include hb hb' hx hq hF hg
lemma peg_cost (hB : ∀ i t, ‖iteratedDeriv i f t‖ ≤ B * P^i) (hY : ∀ i t, ‖iteratedDeriv i g t‖ ≤ B' * Q^i) (t) :
    ‖iteratedDeriv K (f*g) t‖ ≤ B * B' * (P+Q)^K := by
  rw [iteratedDeriv_mul ((hF.of_le (by simp)).contDiffAt) ((hg.of_le (by simp)).contDiffAt),add_pow, Finset.mul_sum]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=> ?_)
  rw [mul_assoc,←nsmul_eq_mul]
  have h := (norm_mul_le ..).trans (mul_le_mul (hB i t) (hY (K-i) t) (norm_nonneg _) (by positivity))
  exact (norm_nsmul_le (a:=iteratedDeriv i f t * iteratedDeriv _ g t) (n:=Nat.choose K i)).trans ((mul_le_mul_of_nonneg_left h (by positivity : 0≤(Nat.choose K i:ℝ))).trans_eq (by ring))
omit hb hb' hx hq hF hg

variable {σ : ℝ}

def allowance (n : ℕ) (σ : ℝ) := (n.factorial:ℝ)*Real.exp 1*((1+2/σ)^n)
lemma allowance_pos (n : ℕ) (hσ : 0 ≤ σ) : 0≤allowance n σ := by unfold allowance; positivity
lemma polynomial_cap (n : ℕ) (σ x : ℝ) (h : 0 < σ) (h₁ : 0 ≤ x) : (1+x)^n ≤ allowance n σ * Real.exp (σ/2*x) := by
  let a := 1+(σ/2)*x; let g:=n.factorial
  have ha : 0≤a := by unfold a; positivity
  have he : 1+x ≤ (1+2/σ)*a := by unfold a; field_simp; nlinarith [sq_nonneg σ]
  have hp := (div_le_iff₀' (by exact_mod_cast Nat.factorial_pos n)).mp (Real.pow_div_factorial_le_exp a ha n)
  calc
    _ ≤ ((1+2/σ)*a)^n := pow_le_pow_left₀ (by positivity) he _
    _ ≤ _ := by rw [mul_pow]; refine (mul_le_mul_of_nonneg_left hp (by positivity : 0≤(1+2/σ)^n)).trans_eq ?_; unfold a allowance; rw [Real.exp_add]; ring

variable {α : Type*}

section weighed
variable {C : ℝ} {W : α→ℝ} {L : α→ℝ} (hW : Carries C σ L W) (hs : 0 < σ)

def cap (n : ℕ) (B P : ℝ) (h : α → ℝ → ℝ) (L : α→ℝ) := ∀ i t (k : ℕ), k ≤ n → ‖iteratedDeriv k (h i) t‖ ≤ B* ((1+L i)*P)^k

set_option maxHeartbeats 100000 in
include hW hs in
lemma weigh_terms (hb : 0≤B) (hx : 0≤P) (h : α→ℝ→ℝ) (n) (ht : cap n B P h L) (hg : ∀ i, ContDiff ℝ ω (h i)) (t : ℝ) :
   (∀ k≤n, Summable (fun i=>‖W i * iteratedDeriv k (h i) t‖)) ∧
     HasSum (fun i=> W i * iteratedDeriv n (h i) t) (iteratedDeriv n (fun t=>∑' i,W i*h i t) t) := by
  let V (i : α) := W i • h i
  let y (k : ℕ) i := B * P^k * allowance k σ * Real.exp (σ/2 * L i) * ‖W i‖
  have hL := hW.1
  have hB i : ContDiff ℝ ω (V i) := ContDiff.const_smul (W i) (hg i)
  have hp i t k : iteratedDeriv k (V i) t = W i * iteratedDeriv k (h i) t := iteratedDeriv_const_smul ((hg i|>.of_le (by simp)).contDiffAt) _
  have ht1 k (hk : k ≤ n) i t : ‖W i*iteratedDeriv k (h i) t‖ ≤ y k i := by
    rw [norm_mul]
    unfold y
    rw [mul_comm _ ‖W i‖]
    apply mul_le_mul_of_nonneg_left ((ht i t k hk).trans _) (norm_nonneg _)
    rw [mul_pow, ←mul_assoc B _ (P^k),mul_right_comm B _ (P^k), mul_assoc (B * P^k) _ (rexp (σ/2*L i))]
    exact mul_le_mul_of_nonneg_left (polynomial_cap k σ (L i) hs (hL i)) (by positivity)
  have hx': ∀ k,Summable (y k) := fun k=> (hW.summable_norm hs (B*P^k*allowance k σ) (fun i => show ‖y k i‖≤_ from by rw [Real.norm_of_nonneg (by unfold y; positivity [allowance_pos k hs.le])])).of_norm
  have ht' := fun k hk => Summable.of_nonneg_of_le (fun i => norm_nonneg _) (ht1 k hk · t) (hx' k)
  refine ⟨ht', ?_⟩ -- wrong
  -- thru CLM evaluation at n identical unit directions
  have hFF (k:ℕ) i t : (k:ℕ∞) ≤ n → ‖iteratedFDeriv ℝ k (V i) t‖ ≤ y k i := fun h=> by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hp]; exact ht1 k (by simpa using! h) i t
  let r := (fun _ : Fin n => (1:ℝ))
  change HasSum _ (iteratedDeriv n (fun t=> ∑' i, V i t) t)
  rw [iteratedDeriv_eq_iteratedFDeriv,iteratedFDeriv_tsum_apply (f:=V) (k:=n) (N:=(n:ℕ∞)) (fun i=> (hB i).of_le (by simp)) (fun k hk=>hx' k) hFF le_rfl]
  let S i := iteratedFDeriv ℝ n (V i) t
  change HasSum _ ((∑' i,S i) r)
  have hs' : Summable S := Summable.of_norm_bounded (hx' n) (fun i=>hFF n i t le_rfl)
  rw [show ((∑' i,S i) r) = ∑' i, S i r from (ContinuousMultilinearMap.apply ℝ _ _ r).map_tsum hs']
  change HasSum _ (∑' i,iteratedDeriv n (V i) t)
  simp_rw [hp]; exact (ht' n le_rfl).of_norm.hasSum

/-- n is either 3 or 4; leave reserve for the constant 1 in the weight. -/
def gain (D Y : ℝ) (n : ℕ) := if n=3 then D^3 else D*Y^3
lemma gain_pos {D Y : ℝ} {n} (hD : 0 ≤ D) (hY : 0 ≤ Y) : 0≤gain D Y n := by unfold gain; split <;> positivity


set_option maxHeartbeats 100000 in
include hW hs in
lemma weigh_bill (h : α→ℝ→ℝ) (B Z : ℝ) (hB : 0≤B) (hZ : 0≤Z) (t : ℝ) (h₀ : ∀ i, |iteratedDeriv K (h i) t| ≤ B*(1+L i)^K * Z) : ∀ s : Finset α,
    |∑ i∈s, W i*iteratedDeriv K (h i) t| ≤ B * allowance K σ * Z * C := by
  intro s
  have hP := allowance_pos K hs.le
  calc
    _ ≤ (B * allowance K σ * Z) * ∑ i∈s, Real.exp (σ*L i) * ‖W i‖ := by
      rw [Finset.mul_sum]; refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=>?_) -- abs_sum_le_sum_abs signature
      rw [abs_mul,←Real.norm_eq_abs]
      have hh := polynomial_cap K σ (L i) hs (hW.1 _)
      have hP' := hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by have hL:=hW.1 i; nlinarith : σ/2*L i ≤ σ*L i)) hP)
      exact (mul_le_mul_of_nonneg_left ((h₀ i).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP' hB) hZ)) (norm_nonneg _)).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left (hW.2 _) (by positivity)

end weighed

end YM.UVExt.Paths
