import YM.FormalOPE.RG10.Rupture.Contraction
/-!
 # All rooted powers after shift. Use any Tier (including exponentials);
 Rank envelope through k picked separately for each mark but even inherited along.S.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Rupture
open Function PowerSeries Finset Route HStein Tier Multi.Vacuum.Gauss Primitives.GCC.LocalPolynomial
open scoped Topology BigOperators Classical
variable {I B J X:Type} [Fintype J]
variable {q:I→Row J}{V:Channel (I⊕B)}{p:I⊕B→X}{F:Tier}
local notation "P"=>Packet (I⊕B)
local notation "W"=>Channel (I⊕B)
local notation "Z"=> Index I B
variable {T:Tape X} (O A E:Lens T){C L:ℝ}{d i r k s t:ℕ}
local notation "A₁"=> A.m ∘ p
local notation "E₁"=> E.m ∘ p
local notation "wB"=> O.m ∘ (p ∘ Sum.inr)
local notation "Bf"=> C^(10*d)
local notation "♥"=>F.value L
local notation "φ"=> tall F (d+1)
variable (hh:PaidPair q V T p F C L O A E r d)(hL:0≤L)
include hh hL
lemma bon (f g:P)(h : k≤r)(ht: f.totalDegree +g.totalDegree+3*k ≤ d) : ♥* F.valueOf wB (foot q V k (PowerSeries.C g) f) ≤ Bf*((φ).valueOf A₁ f*(φ).valueOf E₁ g):= by
 have h0:= F.cp hL
 nth_rw 1 [resolves f]; rw [map_sum]; apply (mul_le_mul_of_nonneg_left (F.many _ (nout O p) _ _) h0).trans;
 rw [(φ).capital A₁ (nnews A p), (φ).capital E₁ (nnews E p), mul_sum,sum_mul_sum,mul_sum]; apply sum_le_sum; intro i hi;
 rw [map_smul,Tier.coins, swapped]; nth_rw 1 [resolves g]; rw [map_sum,mul_left_comm]; apply le_trans (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (F.many _ (nout O p) _ _) h0)) (norm_nonneg _)); rw [mul_sum,mul_sum,mul_sum]; apply sum_le_sum; intro j hj; rw [map_smul, Tier.coins,swapped, mul_left_comm ♥];
 have hv := MvPolynomial.le_totalDegree hi; have hu := MvPolynomial.le_totalDegree hj; change length i≤ f.totalDegree at hv; change length j≤g.totalDegree at hu; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh k h i j (by omega)) (norm_nonneg _)) (norm_nonneg _)).trans; rw [mul_pow]; apply le_of_eq; unfold tall face; simp only; ring
omit hh hL

private lemma area (C : ℝ)(T₁ : ℝ) {r k:ℕ}{I : ℕ×ℕ→ℝ} (hh: (r+1:ℝ)≤C)(ht: 0≤ T₁) (hr:k≤r) (he:∀ i∈ antidiagonal k,I i ≤ T₁): ∑ i∈ antidiagonal k,I i ≤ C*T₁:= by
 apply (sum_le_sum he).trans; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ _ => T₁), sum_const,nsmul_eq_mul,card_range]; push_cast; exact mul_le_mul_of_nonneg_right ((add_le_add_left (Nat.cast_le.mpr hr) 1).trans hh) ht
variable (f g:Channel (I⊕B)) (hc:2 ≤ C) (hr:(r+1:ℝ)≤C)
variable (ht: s+t+3*r≤d)(he:Guard f r s)(hf:Guard g r t)
include hh hL ht he hf hc hr
def geese (d:ℕ):=10*d+3
theorem grain : ♥ * F.gain wB (split q V g f) r ≤ C^geese d*((tall F (d+1)).gain A₁ f r)* ((tall F (d+1)).gain E₁ g r):= by
 let S:=(φ).gain A₁ f r; let U:=(φ).gain E₁ g r; have hU:0≤U:= Tier.collect _ _ (nnews E p) _; have hS:0≤S:=Tier.collect _ _ (nnews A p) _; have h0:0≤ C:= by linarith
 have hp:= F.cp hL
 let u:=Bf*(S*U); have hu: 0≤u:=by unfold u; positivity; -- inspect
 rw [F.all_gain,mul_sum]; apply le_trans (b:=∑ i∈range (r+1),C*(C*u)) (sum_le_sum fun i hi=> ?_) ?_
 · rw [sum_const,nsmul_eq_mul,card_range]; push_cast; refine (mul_le_mul_of_nonneg_right hr (by positivity)).trans (le_of_eq ?_); unfold u S U geese; rw [pow_add];ring
 have hi' :i≤r:=Nat.le_of_lt_succ (mem_range.mp hi);
 rw [thorough]; apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) hp).trans; rw [mul_sum]; apply area C _ hr (by positivity) hi'; intro x hx; have he' := mem_antidiagonal.mp hx
 apply (mul_le_mul_of_nonneg_left (many F _ (nout O p) _ _) hp).trans; rw [mul_sum]; apply area C _ hr hu (by omega : x.2 ≤ r); intro y hy;
 have hy' := mem_antidiagonal.mp hy; have ha:x.1≤ r:= by omega
 have hb:y.1≤r:= by omega
 apply (bon O A E hh hL _ _ (by omega : y.2 ≤ r) (by have hu:= he x.1 ha; have hv:=hf y.1 hb; omega)).trans; apply mul_le_mul_of_nonneg_left _ (pow_nonneg h0 _)
 exact mul_le_mul (Tier.now _ _ (nnews A p) _ ha) (Tier.now _ _ (nnews E p) _ hb) (Tier.lower _ _ (nnews E p) _) hS
omit ht he hf hr hL hh
end YM.FormalOPE.RG10.Rupture
