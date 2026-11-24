import YM.RG12.Budget.Logs
/-!
# Finite readout budget law: pay hatBeta losses at extra internal order

In particular can use with the graded-frame estimates above even if all their log powers are
spent lifting a remainder to fixed-frame observable units. Expose the crucial coefficient
assumption: they must be bounded with `Lambda` losses in the requested reporting scheme (or
convert by a theorem to those units/g units and such losses). Applying a big transport loss to
each dropped term with no such bound does NOT give this. Norms can already encode the output
engineering/separated geometry. Include *all* inverse/reset powers in p, which mustn't depend
on the internal computed order R in a way that precludes paying it with powers chosen at R.
Does not identify any schemes; feed these estimates into RG05 with that data already frozen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Budget
open Function Filter Pert.Asymptotics Topology Lattice RG
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g beta L nu C D eta:ℝ} {r R p q:ℕ}

lemma pay_back (hg:0<g) (hc:g≤1) (ht:0≤beta) (hb: beta*g^2 ≤3) (he:eta≤1)
    (hR:r+1+2*p ≤ R) : beta^p * g ^ ((R:ℝ)+1-eta) ≤ 3^p * g^(r+1) := by
  have hp : g ^ ((R:ℝ)+1-eta) ≤ g^R:=by rw [← Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_ge hg hc; linarith
  refine (mul_le_mul_of_nonneg_left hp (pow_nonneg ht _)).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le hc hR) (pow_nonneg ht _)).trans ?_)
  rw [pow_add,pow_mul]; calc
    _=(beta*g^2)^p*g^(r+1):=by rw [mul_pow]; ring
    _≤_:= mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb _) (by positivity)

/-- Completely finite intermediate expansion, already 
in the output coefficient family. The extra-order gap can accommodate one whole power of
eta slack as well as `p` lost hatBeta powers, with an explicit constant degradation.
For different log powers in the two assumptions can always take larger on the tail by
L ≥ 1. -/
theorem afford (hg:0<g) (hc:g≤1) (ht:0≤beta) (hb:beta*g^2 ≤3)
    (hn:0≤nu) (hL:0≤L) (hC:0≤C)(he:eta≤1) (hR:r+1+2*p ≤ R)
    (physical:E) (A:ℕ→E)
    (hX: ‖physical - ∑ k∈Finset.range (R+1), (g^k:ℝ) • A k‖ ≤ C * beta^p * g ^ ((R:ℝ)+1-eta) * L^q * nu)
    (hA:∀ k:ℕ, r < k → k ≤ R → ‖A k‖ ≤ D*L^q*nu) :
    ‖physical-∑ k∈Finset.range (r+1), (g^k:ℝ) • A k‖ ≤ (C*3^p+(R-r:ℕ)*D)*g^(r+1)*L^q*nu := by
  have hh:r≤R:=by omega
  let T:=Finset.range (R+1); let S:=Finset.range (r+1)
  have hST:S ⊆ T:= Finset.range_mono (by omega)
  let f k:= (g^k:ℝ) • A k
  change ‖physical - ∑ k ∈ S,f k‖ ≤ _
  change ‖physical - ∑ k ∈ T,f k‖ ≤ _ at hX
  have hφ: physical - ∑ k ∈ S,f k = (physical - ∑ k ∈ T,f k)+∑ k∈T\S,f k:=by rw [← Finset.sum_sdiff hST]; abel
  rw [hφ]; apply (norm_add_le ..).trans
  have hs : 0 ≤ L^q * nu:=by positivity
  have hx: ‖physical-∑ k∈T,f k‖ ≤ C*3^p*g^(r+1)*L^q*nu:=by
    apply hX.trans
    calc
      _=C*(beta^p*g ^ ((R:ℝ)+1-eta))*(L^q*nu):=by ring
      _≤ C*(3^p*g^(r+1))*(L^q*nu):= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pay_back hg hc ht hb he hR) hC) hs
      _=_:=by ring
  have hu : ‖∑ k∈ T\S,f k‖ ≤ ((R-r:ℕ):ℝ)*D*g^(r+1)*L^q*nu:=by
    calc
      _ ≤ ∑ k∈T\S,D*g^(r+1)*L^q*nu:= (norm_sum_le ..).trans (Finset.sum_le_sum fun k h=> ?_)
      _ = _:=by rw [Finset.sum_const,nsmul_eq_mul,Finset.card_sdiff_of_subset hST]; simp only [T,S,Finset.card_range,Nat.add_sub_add_right]; ring
    obtain ⟨hk,h⟩:=Finset.mem_sdiff.mp h
    have he' : k ≤ R:= Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hy : r+1 ≤ k:=by apply Nat.le_of_not_gt; intro h'; exact h (Finset.mem_range.mpr h')
    unfold f; rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hg.le _)]
    exact (mul_le_mul (pow_le_pow_of_le_one hg.le hc hy) (hA k hy he') (norm_nonneg _) (pow_nonneg hg.le _)).trans_eq (by ring)
  exact (add_le_add hx hu).trans_eq (by ring)

-- `Sample.age` comparison doesn't tolerate an epsilon loss on the leading germ or arbitrary
-- Lambda powers. For evaluating an actual gram (or its polar correlations) on this march:
lemma pay_dilation {I:Type*}{l:Filter I}{g age: I→ℝ}{q:ℕ}{a D E:ℝ}
    (hE:0≤E)(hD:0≤D) (hA:∀ᶠ i in l,age i*(g i)^2 ≤ a ∧ 0 < age i)
    (hg:Tendsto g l (𝓝[>] 0)) : ∀ᶠ i in l, ∀ (old new G₀ G₁ G₂old G₂new nu : ℝ),
      0 ≤ nu →
      -- same first-order readings after positioning or their discrepancy binned with G2
      -- (low-order comparison with one pure coupling power of leftover headroom). Can plug
      -- profile or quadratic test norms for nu.
      |old-(G₀+g i*G₁+(g i)^2*G₂old)| ≤ D*(g i)^3*logPrice (g i)^q*nu →
      |new-(G₀+g i*G₁+(g i)^2*G₂new)| ≤ D*(g i)^3*logPrice (g i)^q*nu →
      |G₂old-G₂new| ≤ E*nu → |old-new| ≤ ((D*2+E)*a/age i)*nu := by
  have hp:= hg.eventually (self_mem_nhdsWithin : ∀ᶠ x:ℝ in 𝓝[>]0,0<x)
  have hf:= ((log_fades q).comp hg).eventually (ge_mem_nhds zero_lt_one)
  filter_upwards [hA,hp,hf] with i hi hpi hfi b c x y z z' nu hn ht hh hz
  obtain ⟨ht1,ht2⟩:=abs_le.mp ht; obtain ⟨hh1,hh2⟩:=abs_le.mp hh; obtain ⟨hz1,hz2⟩:=abs_le.mp hz
  let r:=g i; let s:=logPrice r
  have hu:r*s^q≤1:=hfi
  have he : D*r^3*s^q*nu ≤ D*r^2*nu:= by
    calc
      _=D*r^2*nu*(r*s^q):=by ring
      _≤_:=mul_le_of_le_one_right (by positivity) hu
  have ho : |b-c| ≤ (D*2+E)*r^2*nu:=by
    apply abs_le.mpr
    have hM1:=mul_le_mul_of_nonneg_left hz1 (sq_nonneg r)
    have hM2:=mul_le_mul_of_nonneg_left hz2 (sq_nonneg r)
    dsimp only [r,s] at *
    constructor <;> linarith only [hM1,hM2,ht1,ht2,hh1,hh2,he]
  rw [div_mul_eq_mul_div,le_div_iff₀ hi.2];
  apply (mul_le_mul_of_nonneg_right ho hi.2.le).trans
  convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi.1 (show 0 ≤ D*2+E by positivity)) hn using 1
  unfold r; ring
end YM.RG12.Budget
